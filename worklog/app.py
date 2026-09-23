import io
import os
import re
import sys
import json
import shutil
import uuid
import threading
import mimetypes
import socket
import ipaddress
import urllib.request
from datetime import datetime, date, timedelta
from flask import (Flask, render_template, request, jsonify, session,
                   redirect, url_for, send_file)
from functools import wraps
from werkzeug.security import generate_password_hash, check_password_hash
# ---------------- 打包适配 ----------------
IS_FROZEN = getattr(sys, 'frozen', False)
if IS_FROZEN:
    template_folder = os.path.join(sys._MEIPASS, 'templates')
    app = Flask(__name__, template_folder=template_folder)
    # ★ 数据固定放用户主目录（推荐），或 exe 同目录（看你需求）
    BASE_DIR = os.path.join(os.path.expanduser("~"), "WorkLogData")
    os.makedirs(BASE_DIR, exist_ok=True)
else:
    app = Flask(__name__)
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
# ---------------- 目录规划 ----------------
# logs: 旧版共用日志目录，仅用于首次启动把历史数据迁移给 admin
LOG_DIR = os.path.join(BASE_DIR, "logs")
os.makedirs(LOG_DIR, exist_ok=True)
# data/<用户名>: 每个用户的日志与附件（分用户隔离）
DATA_DIR = os.path.join(BASE_DIR, "data")
os.makedirs(DATA_DIR, exist_ok=True)
# archived: 删除账号时归档的数据
ARCHIVED_DIR = os.path.join(BASE_DIR, "archived")
os.makedirs(ARCHIVED_DIR, exist_ok=True)
USERS_FILE = os.path.join(BASE_DIR, "users.json")
DELETE_RECORDS_FILE = os.path.join(BASE_DIR, "delete_records.json")
SUMMARIES_FILE = os.path.join(BASE_DIR, "summaries.json")
app.secret_key = "change-this-secret-key-please"
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
# ★★★ 用户名正则：允许中文、字母、数字、下划线，长度 2-20 个字符 ★★★
USERNAME_RE = re.compile(r"^[\u4e00-\u9fa5A-Za-z0-9_]{2,20}$")
# ---------------- 工具 ----------------
def today_str():
    return date.today().isoformat()
def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")
def _is_private_ip(ip):
    """判断 IP 是否为内网/保留地址（此类地址无法公网定位）"""
    try:
        import ipaddress
        addr = ipaddress.ip_address(ip)
        return (addr.is_private or addr.is_loopback or addr.is_link_local
                or addr.is_reserved or addr.is_multicast)
    except Exception:
        if ip.startswith(("10.", "192.168.", "127.", "169.254.")):
            return True
        if ip.startswith("172.") and ip.count(".") >= 1:
            try:
                return 16 <= int(ip.split(".")[1]) <= 31
            except ValueError:
                return False
        return False

def _normalize_ip(ip):
    """校验并规范化 IP 字符串（IPv4/IPv6），非法返回 None"""
    if not ip:
        return None
    ip = ip.strip()
    try:
        return str(ipaddress.ip_address(ip))
    except ValueError:
        return None

IP_DETAIL_CACHE = {}
IP_DETAIL_CACHE_LOCK = threading.Lock()

def _empty_detail():
    return {"country": "", "province": "", "city": "", "district": "",
            "isp": "", "lat": "", "lon": "", "source": ""}

def _fetch_ip_detail(ip, timeout):
    """多源查询 IP 归属地，返回结构化 dict 或 None（按精确度降级：腾讯->pconline->ip-api->ip.sb->ipinfo）"""
    # 1) 腾讯位置服务（可到区+经纬度，需环境变量 TX_MAP_KEY）
    tx_key = os.environ.get("TX_MAP_KEY", "").strip()
    if tx_key:
        try:
            url = "https://apis.map.qq.com/ws/location/v1/ip?ip={}&key={}".format(ip, tx_key)
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 WorkLog"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            if data.get("status") == 0:
                result = data.get("result") or {}
                ad = result.get("ad_info") or {}
                loc = result.get("location") or {}
                d = _empty_detail()
                d.update({
                    "country": ad.get("nation", ""),
                    "province": ad.get("province", ""),
                    "city": ad.get("city", ""),
                    "district": ad.get("district", ""),
                    "isp": result.get("isp", ""),
                    "lat": str(loc.get("lat", "")),
                    "lon": str(loc.get("lng", "")),
                    "source": "腾讯位置服务",
                })
                if d["province"] or d["city"] or d["district"]:
                    return d
        except Exception:
            pass
    # 2) pconline（国内、无 key，省/市）
    try:
        url = "http://whois.pconline.com.cn/ipJson.jsp?ip={}&json=true".format(ip)
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 WorkLog"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
        try:
            text = raw.decode("gbk")
        except Exception:
            text = raw.decode("utf-8", "ignore")
        data = json.loads(text)
        if data.get("pro") or data.get("city"):
            d = _empty_detail()
            d.update({
                "province": data.get("pro", ""),
                "city": data.get("city", ""),
                "source": "pconline",
            })
            return d
    except Exception:
        pass
    # 3) ipinfo.io（国际、无 key，省/市；对国内 IP 返回标准英文省/市，优先于 ip-api/ip.sb）
    try:
        url = "https://ipinfo.io/{}/json".format(ip)
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 WorkLog"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        if data.get("city") or data.get("region") or data.get("country"):
            d = _empty_detail()
            loc = (data.get("loc") or "").split(",")
            d.update({
                "country": data.get("country", ""),
                "province": data.get("region", ""),
                "city": data.get("city", ""),
                "isp": data.get("org", ""),
                "lat": loc[0].strip() if len(loc) > 0 else "",
                "lon": loc[1].strip() if len(loc) > 1 else "",
                "source": "ipinfo.io",
            })
            return d
    except Exception:
        pass


def ip_location_detail(ip, timeout=5):
    """查询公网 IP 归属地（结构化：省/市/区/ISP/经纬度，带缓存）"""
    if not ip or ip == "unknown":
        return _empty_detail()
    if _is_private_ip(ip):
        d = _empty_detail()
        d["source"] = "内网/局域网"
        return d
    with IP_DETAIL_CACHE_LOCK:
        if ip in IP_DETAIL_CACHE:
            return IP_DETAIL_CACHE[ip]
    detail = _fetch_ip_detail(ip, timeout)
    if detail is None:
        detail = _empty_detail()
    # 英文/拼音省市 -> 中文（保证与地图 GeoJSON 中文名称一致）
    for _k in ("province", "city", "district"):
        if detail.get(_k):
            detail[_k] = en_to_zh(detail[_k])
    with IP_DETAIL_CACHE_LOCK:
        IP_DETAIL_CACHE[ip] = detail
    return detail

def ip_location(ip, timeout=2):
    """查询公网 IP 归属地（带缓存），返回「省-市-区」或 '未知'；内网地址返回 '内网/局域网'"""
    detail = ip_location_detail(ip, timeout=timeout)
    if detail.get("source") == "内网/局域网":
        return "内网/局域网"
    s = "-".join([p for p in (detail.get("province", ""), detail.get("city", ""),
                               detail.get("district", "")) if p])
    if not s:
        s = detail.get("country", "")
    return s or "未知"

def get_client_ip():
    """
    获取真实客户端 IP（增强版）
    - X-Forwarded-For 多级代理时取第一个（最接近客户端）
    - 依次回退 X-Real-IP、remote_addr
    ⚠️ 如果部署在Nginx/Apache反向代理之后，务必配置：
        proxy_set_header X‑Real‑IP $remote_addr;
        proxy_set_header X‑Forwarded‑For $proxy_add_x_forwarded_for;
    否则只能拿到网关代理IP，无法获取用户真实内网/公网IP；程序无法绕过网关获取原始IP
    """
    xff = request.headers.get("X-Forwarded-For", "")
    if xff:
        parts = [p.strip() for p in xff.split(",") if p.strip()]
        if parts:
            return parts[0]
    xri = request.headers.get("X-Real-IP", "")
    if xri:
        return xri.strip()
    return request.remote_addr or "unknown"

def client_ip_info():
    """
    返回 (客户端IP, 归属地)
    - 优先使用前端在浏览器侧上报的公网出口 IP（session 缓存）
    - 无上报时回退到请求头/remote_addr（可能是内网或代理 IP）
    """
    reported = session.get("client_public_ip")
    if reported:
        return reported, ip_location(reported)
    ip = get_client_ip()
    return ip, ip_location(ip)
def current_ip_detail():
    """返回当前请求客户端的 (IP, 展示地点字符串, 结构化 detail)，供日志写入等场景使用"""
    reported = session.get("client_public_ip")
    ip = reported or get_client_ip()
    detail = ip_location_detail(ip)
    return ip, ip_location(ip), detail
def parse_location(loc):
    """解析 location 字符串（如 广东省-深圳市-南山区 / California-Mountain View），返回 (省, 市)"""
    parts = [x.strip() for x in str(loc or "").split("-") if x.strip()]
    if not parts:
        return "", ""
    return parts[0], (parts[1] if len(parts) > 1 else "")
# 中国地图（DataV GeoJSON 100000_full.json）使用的省级行政区全称
PROVINCE_ALIAS_MAP = {
    "北京": "北京市", "北京市": "北京市",
    "天津": "天津市", "天津市": "天津市",
    "上海": "上海市", "上海市": "上海市",
    "重庆": "重庆市", "重庆市": "重庆市",
    "河北": "河北省", "河北省": "河北省",
    "山西": "山西省", "山西省": "山西省",
    "内蒙古": "内蒙古自治区", "内蒙古自治区": "内蒙古自治区",
    "辽宁": "辽宁省", "辽宁省": "辽宁省",
    "吉林": "吉林省", "吉林省": "吉林省",
    "黑龙江": "黑龙江省", "黑龙江省": "黑龙江省",
    "江苏": "江苏省", "江苏省": "江苏省",
    "浙江": "浙江省", "浙江省": "浙江省",
    "安徽": "安徽省", "安徽省": "安徽省",
    "福建": "福建省", "福建省": "福建省",
    "江西": "江西省", "江西省": "江西省",
    "山东": "山东省", "山东省": "山东省",
    "河南": "河南省", "河南省": "河南省",
    "湖北": "湖北省", "湖北省": "湖北省",
    "湖南": "湖南省", "湖南省": "湖南省",
    "广东": "广东省", "广东省": "广东省",
    "广西": "广西壮族自治区", "广西壮族自治区": "广西壮族自治区",
    "海南": "海南省", "海南省": "海南省",
    "四川": "四川省", "四川省": "四川省",
    "贵州": "贵州省", "贵州省": "贵州省",
    "云南": "云南省", "云南省": "云南省",
    "西藏": "西藏自治区", "西藏自治区": "西藏自治区",
    "陕西": "陕西省", "陕西省": "陕西省",
    "甘肃": "甘肃省", "甘肃省": "甘肃省",
    "青海": "青海省", "青海省": "青海省",
    "宁夏": "宁夏回族自治区", "宁夏回族自治区": "宁夏回族自治区",
    "新疆": "新疆维吾尔自治区", "新疆维吾尔自治区": "新疆维吾尔自治区",
    "台湾": "台湾省", "台湾省": "台湾省",
    "香港": "香港特别行政区", "香港特别行政区": "香港特别行政区",
    "澳门": "澳门特别行政区", "澳门特别行政区": "澳门特别行政区",
}
def normalize_province_name(p):
    """将省份简称/常见写法归一化为中国地图（DataV GeoJSON）使用的全称，确保地图着色与 tooltip 匹配"""
    p = (str(p or "")).strip()
    return PROVINCE_ALIAS_MAP.get(p, p)
# IP 定位英文/拼音结果 -> 中文（ip.sb / ipinfo.io 等源返回英文省市，需翻译以保证与地图中文名称匹配）
EN_CN_MAP = {
    # 省级
    "beijing": "北京", "tianjin": "天津", "shanghai": "上海", "chongqing": "重庆",
    "hebei": "河北", "shanxi": "山西", "neimenggu": "内蒙古", "innermongolia": "内蒙古",
    "liaoning": "辽宁", "jilin": "吉林", "heilongjiang": "黑龙江",
    "jiangsu": "江苏", "zhejiang": "浙江", "anhui": "安徽", "fujian": "福建", "jiangxi": "江西",
    "shandong": "山东", "henan": "河南", "hubei": "湖北", "hunan": "湖南", "guangdong": "广东",
    "guangxi": "广西", "hainan": "海南", "sichuan": "四川", "guizhou": "贵州", "yunnan": "云南",
    "tibet": "西藏", "xizang": "西藏", "shaanxi": "陕西", "gansu": "甘肃", "qinghai": "青海",
    "ningxia": "宁夏", "xinjiang": "新疆", "taiwan": "台湾",
    "hongkong": "香港", "macau": "澳门", "macao": "澳门",
    # 常用城市
    "shijiazhuang": "石家庄", "taiyuan": "太原", "datong": "大同", "linfen": "临汾",
    "hohhot": "呼和浩特", "huhehaote": "呼和浩特", "baotou": "包头", "ordos": "鄂尔多斯",
    "shenyang": "沈阳", "dalian": "大连", "anshan": "鞍山", "dandong": "丹东", "jinzhou": "锦州",
    "changchun": "长春", "siping": "四平", "tonghua": "通化", "yanji": "延吉",
    "harbin": "哈尔滨", "qiqihar": "齐齐哈尔", "daqing": "大庆", "jiamusi": "佳木斯", "mudanjiang": "牡丹江",
    "nanjing": "南京", "wuxi": "无锡", "xuzhou": "徐州", "changzhou": "常州", "suzhou": "苏州",
    "nantong": "南通", "lianyungang": "连云港", "yangzhou": "扬州", "zhenjiang": "镇江",
    "hangzhou": "杭州", "ningbo": "宁波", "wenzhou": "温州", "jiaxing": "嘉兴", "huzhou": "湖州",
    "shaoxing": "绍兴", "jinhua": "金华", "quzhou": "衢州", "zhoushan": "舟山",
    "hefei": "合肥", "wuhu": "芜湖", "bengbu": "蚌埠", "huainan": "淮南", "anqing": "安庆", "huangshan": "黄山",
    "fuzhou": "福州", "xiamen": "厦门", "putian": "莆田", "quanzhou": "泉州", "zhangzhou": "漳州", "ningde": "宁德",
    "nanchang": "南昌", "jingdezhen": "景德镇", "jiujiang": "九江", "ganzhou": "赣州",
    "jinan": "济南", "qingdao": "青岛", "zibo": "淄博", "yantai": "烟台", "weifang": "潍坊",
    "jining": "济宁", "weihai": "威海", "rizhao": "日照", "linyi": "临沂", "dezhou": "德州", "liaocheng": "聊城", "heze": "菏泽",
    "zhengzhou": "郑州", "kaifeng": "开封", "luoyang": "洛阳", "anyang": "安阳", "xinxiang": "新乡",
    "jiaozuo": "焦作", "xuchang": "许昌", "nanyang": "南阳", "shangqiu": "商丘", "zhoukou": "周口", "zhumadian": "驻马店",
    "wuhan": "武汉", "huangshi": "黄石", "shiyan": "十堰", "yichang": "宜昌", "xiangyang": "襄阳",
    "jingmen": "荆门", "xiaogan": "孝感", "jingzhou": "荆州", "huanggang": "黄冈", "xianning": "咸宁",
    "changsha": "长沙", "zhuzhou": "株洲", "xiangtan": "湘潭", "hengyang": "衡阳", "shaoyang": "邵阳",
    "yueyang": "岳阳", "changde": "常德", "zhangjiajie": "张家界", "chenzhou": "郴州", "huaihua": "怀化", "loudi": "娄底",
    "guangzhou": "广州", "shenzhen": "深圳", "zhuhai": "珠海", "shantou": "汕头", "foshan": "佛山",
    "shaoguan": "韶关", "zhanjiang": "湛江", "zhaoqing": "肇庆", "jiangmen": "江门", "maoming": "茂名",
    "huizhou": "惠州", "meizhou": "梅州", "shanwei": "汕尾", "heyuan": "河源", "yangjiang": "阳江",
    "qingyuan": "清远", "dongguan": "东莞", "zhongshan": "中山", "chaozhou": "潮州", "jieyang": "揭阳", "yunfu": "云浮",
    "nanning": "南宁", "liuzhou": "柳州", "guilin": "桂林", "wuzhou": "梧州", "beihai": "北海",
    "qinzhou": "钦州", "guigang": "贵港", "baise": "百色", "hezhou": "贺州", "hechi": "河池", "laibin": "来宾", "chongzuo": "崇左",
    "haikou": "海口", "sanya": "三亚", "danzhou": "儋州",
    "chengdu": "成都", "zigong": "自贡", "panzhihua": "攀枝花", "luzhou": "泸州", "deyang": "德阳",
    "mianyang": "绵阳", "guangyuan": "广元", "suining": "遂宁", "neijiang": "内江", "leshan": "乐山",
    "nanchong": "南充", "meishan": "眉山", "yibin": "宜宾", "guangan": "广安", "dazhou": "达州", "bazhong": "巴中",
    "guiyang": "贵阳", "liupanshui": "六盘水", "zunyi": "遵义", "anshun": "安顺", "bijie": "毕节", "tongren": "铜仁",
    "kunming": "昆明", "qujing": "曲靖", "yuxi": "玉溪", "baoshan": "保山", "zhaotong": "昭通",
    "lijiang": "丽江", "puer": "普洱", "lincang": "临沧", "xishuangbanna": "西双版纳", "dali": "大理",
    "lhasa": "拉萨", "lasa": "拉萨", "xigaze": "日喀则", "nyingchi": "林芝", "shannan": "山南", "chamdo": "昌都",
    "xian": "西安", "xi'an": "西安", "tongchuan": "铜川", "baoji": "宝鸡", "xianyang": "咸阳",
    "weinan": "渭南", "yanan": "延安", "hanzhong": "汉中", "ankang": "安康", "shangluo": "商洛",
    "lanzhou": "兰州", "jiayuguan": "嘉峪关", "jinchang": "金昌", "baiyin": "白银", "tianshui": "天水",
    "wuwei": "武威", "zhangye": "张掖", "pingliang": "平凉", "jiuquan": "酒泉", "qingyang": "庆阳", "dingxi": "定西",
    "xining": "西宁", "haidong": "海东", "yushu": "玉树",
    "yinchuan": "银川", "shizuishan": "石嘴山", "wuzhong": "吴忠", "guyuan": "固原", "zhongwei": "中卫",
    "urumqi": "乌鲁木齐", "wulumuqi": "乌鲁木齐", "kelamayi": "克拉玛依", "tulufan": "吐鲁番", "hami": "哈密",
    "changji": "昌吉", "aksu": "阿克苏", "kashi": "喀什", "hetian": "和田",
    "taipei": "台北", "kaohsiung": "高雄", "taichung": "台中", "tainan": "台南", "hsinchu": "新竹", "keelung": "基隆",
}
def en_to_zh(text):
    """把 IP 定位返回的英文/拼音省市名翻译为中文；无法识别则原样返回"""
    if not text:
        return text
    t = str(text).strip()
    key = re.sub(r"[\s\-'’`]+", "", t).lower()
    return EN_CN_MAP.get(key, t)
def normalize_location(loc):
    """规整用户填写的地址字符串为「省-市」统一格式（去除空白，统一分隔符），无效返回 ''"""
    if not loc:
        return ""
    s = re.sub(r"[\s\u3000]+", "", str(loc))
    s = re.sub(r"[—–_/、，,。.]+", "-", s)
    s = re.sub(r"-+", "-", s).strip("-")
    return s[:50]
def normalize_username(u: str) -> str:
    """用户名归一化：
    - 去掉首尾空白（含全角空格 \u3000）
    - 去掉所有内部空白（含全角），避免 '张 三' 与 '张三' 被当成两个人
    """
    if not u:
        return ""
    # 去掉所有空白字符（普通空格、\t、\n、全角空格）
    return re.sub(r"[\s\u3000]+", "", u)
# ---------------- 用户持久化 ----------------
def load_users():
    """读取用户数据文件（用户名 -> 记录）"""
    if not os.path.exists(USERS_FILE):
        return {}
    try:
        with open(USERS_FILE, "r", encoding="utf-8") as fp:
            data = json.load(fp)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}
def save_users(users):
    """原子写入用户数据文件"""
    tmp = USERS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fp:
        json.dump(users, fp, ensure_ascii=False, indent=2)
    os.replace(tmp, USERS_FILE)
def find_user_case_insensitive(users, u):
    """在 users 里大小写不敏感地查找真实用户名，返回真实 key 或 None"""
    if not u:
        return None
    for exist_u in users.keys():
        if exist_u.lower() == u.lower():
            return exist_u
    return None
def seed_default_users():
    """首次运行创建默认账号：admin（唯一管理员）、user（普通用户示例）"""
    users = load_users()
    changed = False
    if "admin" not in users:
        users["admin"] = {
            "password_hash": generate_password_hash("123456"),
            "role": "admin",
            "created_at": now_str(),
        }
        changed = True
    if "user" not in users:
        users["user"] = {
            "password_hash": generate_password_hash("user123"),
            "role": "user",
            "created_at": now_str(),
        }
        changed = True
    if changed:
        save_users(users)
    return users
def migrate_legacy_logs():
    """把旧版 LOG_DIR(logs) 下的历史日志迁移为 admin 的数据（兼容迁移）"""
    if not os.path.isdir(LOG_DIR):
        return
    has_data = any(
        os.path.isdir(os.path.join(LOG_DIR, n)) and DATE_RE.match(n) and
        os.path.exists(os.path.join(LOG_DIR, n, "log.md"))
        for n in os.listdir(LOG_DIR)
    )
    if not has_data:
        return
    target = os.path.join(DATA_DIR, "admin")
    if os.path.isdir(target) and any(
        os.path.isdir(os.path.join(target, n)) and DATE_RE.match(n)
        for n in os.listdir(target)
    ):
        return  # admin 已有数据，跳过迁移
    os.makedirs(target, exist_ok=True)
    moved = 0
    for n in os.listdir(LOG_DIR):
        src = os.path.join(LOG_DIR, n)
        dst = os.path.join(target, n)
        if os.path.isdir(src) and DATE_RE.match(n) and not os.path.exists(dst):
            shutil.move(src, dst)
            moved += 1
    if moved:
        print(f"[WorkLog] 已迁移 {moved} 条历史日志到 admin 数据目录")
# ---------------- 删除记录持久化 ----------------
def load_delete_records():
    """读取删除账号的记录列表"""
    if not os.path.exists(DELETE_RECORDS_FILE):
        return []
    try:
        with open(DELETE_RECORDS_FILE, "r", encoding="utf-8") as fp:
            data = json.load(fp)
        return data if isinstance(data, list) else []
    except Exception:
        return []
def save_delete_records(records):
    """原子写入删除记录"""
    tmp = DELETE_RECORDS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fp:
        json.dump(records, fp, ensure_ascii=False, indent=2)
    os.replace(tmp, DELETE_RECORDS_FILE)
# ---------------- 登录校验 ----------------
def login_required(f):
    @wraps(f)
    def wrapper(*a, **kw):
        if "user" not in session:
            if request.path.startswith("/api/"):
                return jsonify({"ok": False, "msg": "未登录"}), 401
            return redirect(url_for("login"))
        return f(*a, **kw)
    return wrapper
def admin_required(f):
    @wraps(f)
    def wrapper(*a, **kw):
        if "user" not in session:
            return jsonify({"ok": False, "msg": "未登录"}), 401
        if session.get("role") != "admin":
            return jsonify({"ok": False, "msg": "无权限"}), 403
        return f(*a, **kw)
    return wrapper
def resolve_target():
    """返回本次请求操作的用户名；admin 可通过 ?user=xxx 查看他人数据，不能修改他人数据；
    普通用户永远只能操作自己。
    """
    me = session.get("user")
    if not me:
        return None
    u = request.args.get("user") or me
    users = load_users()
    u_norm = normalize_username(u)
    real_u = find_user_case_insensitive(users, u_norm)
    if not real_u:
        return None
    if real_u != me and session.get("role") != "admin":
        return None
    return real_u
# ---------------- 分用户路径 ----------------
def user_dir(u):     return os.path.join(DATA_DIR, u)
def day_dir(u, d):   return os.path.join(user_dir(u), d)
def day_file(u, d):  return os.path.join(day_dir(u, d), "log.md")
def files_dir(u, d): return os.path.join(day_dir(u, d), "files")
def read_day(u, d):
    """读取某个用户的某天结构化日志（front-matter + body）"""
    f = day_file(u, d)
    if not os.path.exists(f):
        return None
    with open(f, "r", encoding="utf-8") as fp:
        content = fp.read()
    meta, body_lines, in_meta = {}, [], False
    for line in content.splitlines():
        if line.strip() == "---":
            in_meta = not in_meta
            continue
        if in_meta and ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip()
        elif not in_meta:
            body_lines.append(line)
    meta["body"] = "\n".join(body_lines).strip()
    return meta
def write_day(u, d, title, body, status, done, location="", ip=""):
    os.makedirs(day_dir(u, d), exist_ok=True)
    meta_lines = [
        f"title: {title}",
        f"date: {d}",
        f"time: {now_str()}",
        f"status: {status}",
        f"done: {done}",
    ]
    if location:
        meta_lines.append(f"location: {location}")
    if ip:
        meta_lines.append(f"ip: {ip}")
    content = "---\n" + "\n".join(meta_lines) + f"\n---\n{body}\n"
    with open(day_file(u, d), "w", encoding="utf-8") as fp:
        fp.write(content)
def update_day_location(u, d, location, ip):
    """更新某天日志 front-matter 中的地点/IP（保留标题/正文/状态等其他字段），返回是否更新"""
    meta = read_day(u, d)
    if not meta:
        return False
    if not location and not ip:
        return False
    write_day(u, d, meta.get("title", ""), meta.get("body", ""),
              meta.get("status", "进行中"), int(meta.get("done", 0) or 0),
              location=meta.get("location", "") or location,
              ip=ip or meta.get("ip", ""))
    return True
def list_attachments(u, d):
    """列出某用户某天 files/ 目录下的附件"""
    fd = files_dir(u, d)
    if not os.path.isdir(fd):
        return []
    out = []
    for name in sorted(os.listdir(fd)):
        p = os.path.join(fd, name)
        if not os.path.isfile(p):
            continue
        mime, _ = mimetypes.guess_type(name)
        out.append({
            "name": name,
            "size": os.path.getsize(p),
            "mime": mime or "application/octet-stream",
            "text": (mime or "").startswith("text/") or
                    name.lower().endswith((".md", ".txt", ".json", ".csv",
                                           ".py", ".log", ".xml", ".yml", ".yaml")),
            "image": (mime or "").startswith("image/"),
        })
    return out
def safe_join(root, name):
    """防止路径穿越"""
    name = os.path.basename(name)
    return os.path.join(root, name)
def count_logs(ud):
    """统计某用户目录下的日志天数"""
    if not os.path.isdir(ud):
        return 0
    return sum(
        1 for n in os.listdir(ud)
        if os.path.isdir(os.path.join(ud, n)) and DATE_RE.match(n) and
           os.path.exists(os.path.join(ud, n, "log.md"))
    )
def count_attachments(ud):
    """统计某用户目录下的附件数量"""
    if not os.path.isdir(ud):
        return 0
    total = 0
    for n in os.listdir(ud):
        p = os.path.join(ud, n, "files")
        if os.path.isdir(p):
            total += sum(1 for f in os.listdir(p) if os.path.isfile(os.path.join(p, f)))
    return total
def dir_size(ud):
    """统计某用户目录占用空间（字节）"""
    total = 0
    for root, _dirs, files in os.walk(ud):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    return total
# ---------------- 页面 ----------------
@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        data = request.get_json(silent=True) or {}
        raw_u = data.get("username") or ""
        u = normalize_username(raw_u)
        p = data.get("password") or ""
        users = load_users()
        real_u = find_user_case_insensitive(users, u)
        rec = users.get(real_u) if real_u else None
        if rec and check_password_hash(rec.get("password_hash", ""), p):
            session["user"] = real_u
            session["role"] = rec.get("role", "user")
            ip, loc = client_ip_info()
            print(f"[WorkLog] 登录成功 user={real_u} ip={ip} ({loc}) at={now_str()}")
            return jsonify({"ok": True, "role": rec.get("role", "user")})
        ip, loc = client_ip_info()
        print(f"[WorkLog] 登录失败 user={raw_u} ip={ip} ({loc}) at={now_str()}")
        return jsonify({"ok": False, "msg": "账号或密码错误"}), 401
    return render_template("login.html")
@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        data = request.get_json(silent=True) or {}
        raw_u = data.get("username") or ""
        u = normalize_username(raw_u)
        p = data.get("password") or ""
        p2 = data.get("confirm") or ""
        if not USERNAME_RE.match(u):
            return jsonify({"ok": False, "msg": "用户名需为 2-20 位中文/字母/数字/下划线"}), 400
        if len(p) < 6:
            return jsonify({"ok": False, "msg": "密码至少 6 位"}), 400
        if p != p2:
            return jsonify({"ok": False, "msg": "两次输入的密码不一致"}), 400
        users = load_users()
        if find_user_case_insensitive(users, u):
            return jsonify({"ok": False, "msg": f"用户名「{u}」已存在，请更换"}), 400
        if u.lower() == "admin":
            return jsonify({"ok": False, "msg": "该用户名已被保留"}), 400
        users[u] = {
            "password_hash": generate_password_hash(p),
            "role": "user",
            "created_at": now_str(),
        }
        save_users(users)
        os.makedirs(user_dir(u), exist_ok=True)
        ip, loc = client_ip_info()
        print(f"[WorkLog] 注册成功 user={u} ip={ip} ({loc}) at={now_str()}")
        return jsonify({"ok": True})
    return render_template("register.html")
@app.route("/logout")
def logout():
    u = session.get("user", "?")
    ip, loc = client_ip_info()
    print(f"[WorkLog] 退出登录 user={u} ip={ip} ({loc}) at={now_str()}")
    session.clear()
    return redirect(url_for("login"))
@app.route("/api/ip-info")
def api_ip_info():
    """无需登录：返回当前访问者的 IP 与归属地（登录/注册页展示）"""
    ip, loc = client_ip_info()
    detail = ip_location_detail(ip)
    return jsonify({"ok": True, "ip": ip, "location": loc, "detail": detail})

@app.route("/api/report-ip", methods=["POST"])
def api_report_ip():
    """接收前端在浏览器侧获取的公网出口 IP（及浏览器侧定位结果），写入 session 与缓存并返回归属地"""
    data = request.get_json(silent=True) or {}
    ip = _normalize_ip(data.get("ip", ""))
    if not ip:
        return jsonify({"ok": False, "msg": "IP 地址格式无效"}), 400
    session["client_public_ip"] = ip
    # 浏览器侧定位结果（省/市/国家任一非空才采纳），写入缓存，避免服务器在受限网络下访问外部定位源
    detail = data.get("detail")
    if isinstance(detail, dict) and (detail.get("province") or detail.get("city") or detail.get("country")):
        d = _empty_detail()
        d.update({
            "country": str(detail.get("country", "") or ""),
            "province": str(detail.get("province", "") or ""),
            "city": str(detail.get("city", "") or ""),
            "district": str(detail.get("district", "") or ""),
            "isp": str(detail.get("isp", "") or ""),
            "lat": str(detail.get("lat", "") or ""),
            "lon": str(detail.get("lon", "") or ""),
            "source": str(detail.get("source", "") or "浏览器上报"),
        })
        # 与 ip_location_detail 保持一致的英文/拼音 -> 中文转换
        for _k in ("province", "city", "district"):
            if d.get(_k):
                d[_k] = en_to_zh(d[_k])
        with IP_DETAIL_CACHE_LOCK:
            IP_DETAIL_CACHE[ip] = d
    detail = ip_location_detail(ip)
    return jsonify({"ok": True, "ip": ip, "location": ip_location(ip), "detail": detail})

@app.route("/api/my-ip")
@login_required
def api_my_ip():
    """登录后：返回当前访问者的 IP 与归属地（首页/管理页展示）"""
    ip, loc = client_ip_info()
    detail = ip_location_detail(ip)
    return jsonify({"ok": True, "ip": ip, "location": loc, "detail": detail})

@app.route("/")
@login_required
def index():
    return render_template(
        "index.html",
        user=session["user"],
        is_admin=(session.get("role") == "admin"),
    )
@app.route("/admin")
@login_required
def admin_page():
    if session.get("role") != "admin":
        return redirect(url_for("index"))
    return render_template("admin.html", user=session["user"], is_admin=True)
# ---------------- API ----------------
@app.route("/api/today")
@login_required
def api_today():
    return jsonify({"today": today_str()})
@app.route("/api/days")
@login_required
def api_days():
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    today = today_str()
    result = []
    ud = user_dir(u)
    if os.path.isdir(ud):
        for name in os.listdir(ud):
            p = os.path.join(ud, name)
            if os.path.isdir(p) and DATE_RE.match(name) and \
               os.path.exists(os.path.join(p, "log.md")):
                meta = read_day(u, name)
                if not meta:
                    continue
                result.append({
                    "date":   name,
                    "title":  meta.get("title", ""),
                    "time":   meta.get("time", ""),
                    "status": meta.get("status", ""),
                    "done":   int(meta.get("done", 0) or 0),
                    "location": meta.get("location", ""),
                    "attachments": len(list_attachments(u, name)),
                    "editable": name <= today,
                })
    result.sort(key=lambda x: x["date"], reverse=True)
    return jsonify({"today": today, "days": result})
@app.route("/api/recent-uploads")
@login_required
def api_recent_uploads():
    """最近上传的附件列表（含所属日期与日志地点），供首页「最近上传」卡片展示"""
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    out = []
    ud = user_dir(u)
    if os.path.isdir(ud):
        for name in os.listdir(ud):
            p = os.path.join(ud, name)
            if not (os.path.isdir(p) and DATE_RE.match(name)):
                continue
            meta = read_day(u, name) or {}
            fd = os.path.join(p, "files")
            if not os.path.isdir(fd):
                continue
            for fn in os.listdir(fd):
                fp = os.path.join(fd, fn)
                if not os.path.isfile(fp):
                    continue
                out.append({
                    "name": fn,
                    "date": name,
                    "mtime": os.path.getmtime(fp),
                    "size": os.path.getsize(fp),
                    "location": meta.get("location", ""),
                })
    out.sort(key=lambda x: x["mtime"], reverse=True)
    return jsonify({"ok": True, "uploads": out[:10]})
@app.route("/api/day/<d>", methods=["GET", "POST"])
@login_required
def api_day(d):
    if not DATE_RE.match(d):
        return jsonify({"ok": False, "msg": "日期格式错误"}), 400
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    today = today_str()
    if request.method == "GET":
        meta = read_day(u, d)
        editable = d <= today and session.get("user") == u
        reason = "" if editable else "已超过当天或为他人日志，仅可查看，不可修改"
        base = {
            "date": d,
            "today": today,
            "editable": editable,
            "reason": reason,
            "attachments": list_attachments(u, d),
        }
        if not meta:
            base.update({"exists": False, "title": "", "body": "",
                         "status": "进行中", "done": 0, "time": "",
                         "location": "", "ip": ""})
            return jsonify(base)
        base.update({
            "exists": True,
            "title":  meta.get("title", ""),
            "body":   meta.get("body", ""),
            "status": meta.get("status", ""),
            "done":   int(meta.get("done", 0) or 0),
            "time":   meta.get("time", ""),
            "location": meta.get("location", ""),
            "ip":     meta.get("ip", ""),
        })
        return jsonify(base)
    # POST保存：仅本人可写，管理员不能修改他人日志
    if session.get("user") != u:
        return jsonify({"ok":False,"msg":"无权修改他人日志"}),403
    if d > today:
        return jsonify({"ok": False, "msg": "不能修改未来的日期"}), 403
    data = request.get_json(silent=True) or {}
    ip, loc, _detail = current_ip_detail()
    # 地址统一使用 IP 定位（已取消手填位置信息功能）
    location = loc
    write_day(
        u, d,
        (data.get("title") or "").strip(),
        (data.get("body")  or "").strip(),
        data.get("status") or "进行中",
        int(data.get("done") or 0),
        location=location,
        ip=ip,
    )
    return jsonify({"ok": True, "location": location, "ip": ip})
# ---------------- 附件 ----------------
@app.route("/api/day/<d>/upload", methods=["POST"])
@login_required
def api_upload(d):
    if not DATE_RE.match(d):
        return jsonify({"ok": False, "msg": "日期格式错误"}), 400
    if d > today_str():
        return jsonify({"ok": False, "msg": "不能给未来日期上传文件"}), 403
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    # 上传只允许本人，管理员不能给别人上传
    if session.get("user") != u:
        return jsonify({"ok":False,"msg":"无权为他人日志上传附件"}),403
    if "file" not in request.files:
        return jsonify({"ok": False, "msg": "没有选择文件"}), 400
    saved = []
    for f in request.files.getlist("file"):
        if not f or not f.filename:
            continue
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_name = os.path.basename(f.filename)
        target = os.path.join(files_dir(u, d), f"{ts}_{safe_name}")
        os.makedirs(files_dir(u, d), exist_ok=True)
        f.save(target)
        saved.append(os.path.basename(target))
    ip, loc, _detail = current_ip_detail()
    if not os.path.exists(day_file(u, d)):
        write_day(u, d, f"上传了 {len(saved)} 个文件", "", "进行中", 0, location=loc, ip=ip)
    else:
        update_day_location(u, d, loc, ip)
    return jsonify({"ok": True, "saved": saved, "location": loc, "ip": ip})
@app.route("/api/day/<d>/file/<path:name>", methods=["GET", "DELETE"])
@login_required
def api_file(d, name):
    if not DATE_RE.match(d):
        return jsonify({"ok": False, "msg": "日期格式错误"}), 400
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    p = safe_join(files_dir(u, d), name)
    if not os.path.exists(p):
        return jsonify({"ok": False, "msg": "文件不存在"}), 404
    if request.method == "DELETE":
        # 删除附件只允许本人
        if session.get("user") != u:
            return jsonify({"ok":False,"msg":"无权删除他人附件"}),403
        if d > today_str():
            return jsonify({"ok": False, "msg": "不能删除未来日期文件"}), 403
        os.remove(p)
        return jsonify({"ok": True})
    # GET：查看 / 下载，管理员可读他人文件
    as_download = request.args.get("download") == "1"
    return send_file(p, as_attachment=as_download, download_name=name)
@app.route("/api/day/<d>/file/<path:name>/raw")
@login_required
def api_file_raw(d, name):
    """返回文本内容，供前端弹窗显示；管理员可读他人文件"""
    if not DATE_RE.match(d):
        return jsonify({"ok": False, "msg": "日期格式错误"}), 400
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    p = safe_join(files_dir(u, d), name)
    if not os.path.exists(p):
        return jsonify({"ok": False, "msg": "文件不存在"}), 404
    if os.path.getsize(p) > 2 * 1024 * 1024:
        return jsonify({"ok": False, "msg": "文件过大，请下载查看"}), 413
    with open(p, "rb") as fp:
        raw = fp.read()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        try:
            text = raw.decode("gbk")
        except UnicodeDecodeError:
            return jsonify({"ok": False, "msg": "二进制文件无法以文本显示"}), 415
    mime, _ = mimetypes.guess_type(name)
    return jsonify({
        "ok": True,
        "name": name,
        "mime": mime or "text/plain",
        "text": text,
    })
# ---------------- 导入 .md ----------------
@app.route("/api/import-md", methods=["POST"])
@login_required
def api_import_md():
    if "file" not in request.files:
        return jsonify({"ok": False, "msg": "未选择文件"}), 400
    f = request.files["file"]
    if not f.filename:
        return jsonify({"ok": False, "msg": "文件名为空"}), 400
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    # 导入仅本人
    if session.get("user") != u:
        return jsonify({"ok":False,"msg":"无权为他人导入"}),403
    content = f.read().decode("utf-8", errors="ignore")
    meta, body_lines, in_meta = {}, [], False
    for line in content.splitlines():
        if line.strip() == "---":
            in_meta = not in_meta
            continue
        if in_meta and ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip()
        elif not in_meta:
            body_lines.append(line)
    body = "\n".join(body_lines).strip()
    d = meta.get("date", "").strip()
    if not DATE_RE.match(d):
        m = re.search(r"(\d{4}-\d{2}-\d{2})", f.filename)
        d = m.group(1) if m else today_str()
    title = meta.get("title", "").strip()
    if not title and not body:
        body = content
    os.makedirs(day_dir(u, d), exist_ok=True)
    meta_lines = [
        f"title: {title}",
        f"date: {d}",
        f"time: {meta.get('time', now_str())}",
        f"status: {meta.get('status', '进行中')}",
        f"done: {meta.get('done', '0')}",
    ]
    if meta.get("location"):
        meta_lines.append(f"location: {meta.get('location', '')}")
    if meta.get("ip"):
        meta_lines.append(f"ip: {meta.get('ip', '')}")
    final = "---\n" + "\n".join(meta_lines) + f"\n---\n{body}\n"
    with open(day_file(u, d), "w", encoding="utf-8") as fp:
        fp.write(final)
    return jsonify({"ok": True, "date": d})
# ---------------- 导出 ----------------
@app.route("/export")
@login_required
def export_log():
    u = resolve_target()
    if not u:
        return jsonify({"ok": False, "msg": "无权访问或用户不存在"}), 403
    lines = [f"# 工作日志汇总（{u}）\n"]
    ud = user_dir(u)
    if os.path.isdir(ud):
        for name in sorted(os.listdir(ud), reverse=True):
            if not DATE_RE.match(name):
                continue
            meta = read_day(u, name)
            if not meta:
                continue
            lines.append(f"## {name}  {meta.get('title','')}")
            lines.append(f"- 时间: {meta.get('time','')}")
            lines.append(f"- 状态: {meta.get('status','')}")
            lines.append(f"- 完成度: {meta.get('done','0')}%")
            if meta.get("location"):
                lines.append(f"- 地点: {meta.get('location','')}")
            atts = list_attachments(u, name)
            if atts:
                lines.append(f"- 附件: " + ", ".join(a["name"] for a in atts))
            lines.append("")
            lines.append(meta.get("body", ""))
            lines.append("\n---\n")
    content = "\n".join(lines)
    return send_file(
        io.BytesIO(content.encode("utf-8")),
        as_attachment=True,
        download_name="log.md",
        mimetype="text/markdown",
    )
# ---------------- admin：用户管理 ----------------
@app.route("/api/admin/users")
@admin_required
def api_admin_users():
    users = load_users()
    out = []
    for u, rec in users.items():
        ud = user_dir(u)
        out.append({
            "username": u,
            "role": rec.get("role", "user"),
            "created_at": rec.get("created_at", ""),
            "log_count": count_logs(ud),
            "attachment_count": count_attachments(ud),
            "data_size": dir_size(ud),
        })
    out.sort(key=lambda x: (x["role"] != "admin", x["username"]))
    return jsonify({"ok": True, "users": out})
@app.route("/api/admin/users/<username>", methods=["DELETE"])
@admin_required
def api_admin_delete_user(username):
    u_norm = normalize_username(username)
    users = load_users()
    real_u = find_user_case_insensitive(users, u_norm)
    if real_u == "admin":
        return jsonify({"ok": False, "msg": "不能删除管理员账号"}), 403
    if not real_u:
        return jsonify({"ok": False, "msg": "用户不存在"}), 404
    username = real_u
    archive_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:6]
    archive_path = os.path.join(ARCHIVED_DIR, archive_id)
    os.makedirs(archive_path, exist_ok=True)
    summary, log_count, att_count = [], 0, 0
    src = user_dir(username)
    if os.path.isdir(src):
        for name in sorted(os.listdir(src)):
            sp = os.path.join(src, name)
            if os.path.isdir(sp) and DATE_RE.match(name):
                meta = read_day(username, name)
                if not meta:
                    continue
                atts = list_attachments(username, name)
                log_count += 1
                att_count += len(atts)
                summary.append({
                    "date": name,
                    "title": meta.get("title", ""),
                    "status": meta.get("status", ""),
                    "done": int(meta.get("done", 0) or 0),
                    "attachments": len(atts),
                    "location": meta.get("location", ""),
                    "body_excerpt": (meta.get("body", "") or "")[:100],
                })
        shutil.move(src, os.path.join(archive_path, "data"))
    # 汇总被删账号日志涉及到的省市（地址字段）
    prov_set, city_set = set(), set()
    for s in summary:
        p, c = parse_location(s.get("location", ""))
        p = normalize_province_name(en_to_zh(p))
        c = en_to_zh(c)
        if p:
            prov_set.add(p)
        if c:
            city_set.add(c)
    records = load_delete_records()
    del_ip, del_loc, del_detail = current_ip_detail()
    records.append({
        "id": archive_id,
        "username": username,
        "deleted_by": session.get("user"),
        "deleted_at": now_str(),
        "ip": del_ip,
        "location": del_loc,
        "ip_location": del_loc,
        "ip_detail": del_detail,
        "user_agent": request.headers.get("User-Agent", ""),
        "archive_path": archive_path,
        "archive_relative": os.path.relpath(archive_path, BASE_DIR),
        "log_count": log_count,
        "attachment_count": att_count,
        "provinces": sorted(prov_set),
        "cities": sorted(city_set),
        "summary": summary,
    })
    save_delete_records(records)
    del users[username]
    save_users(users)
    print(f"[WorkLog] 删除账号 user={username} by={session.get('user')} "
          f"ip={del_ip} ({del_loc}) at={now_str()}")
    return jsonify({
        "ok": True,
        "archive_path": archive_path,
        "log_count": log_count,
        "attachment_count": att_count,
    })
@app.route("/api/admin/delete-records")
@admin_required
def api_admin_delete_records():
    return jsonify({"ok": True, "records": load_delete_records()})
@app.route("/api/admin/location-stats")
@admin_required
def api_admin_location_stats():
    """按地点（省/市）聚合全部用户日志：人数、次数、提交人、提交内容明细"""
    users = load_users()
    prov_map, city_map = {}, {}
    total_logs = located_logs = 0
    for u in users:
        ud = user_dir(u)
        if not os.path.isdir(ud):
            continue
        for name in sorted(os.listdir(ud)):
            p = os.path.join(ud, name)
            if not (os.path.isdir(p) and DATE_RE.match(name)):
                continue
            meta = read_day(u, name)
            if not meta:
                continue
            total_logs += 1
            loc = (meta.get("location") or "").strip()
            if not loc or loc in ("内网/局域网", "无法定位", "未知"):
                continue
            province, city = parse_location(loc)
            province = normalize_province_name(en_to_zh(province))
            city = en_to_zh(city)
            if not province:
                continue
            located_logs += 1
            prov = prov_map.setdefault(province, {"province": province, "count": 0, "users": set(), "cities": set(), "days": []})
            prov["count"] += 1
            prov["users"].add(u)
            if city:
                prov["cities"].add(city)
            prov["days"].append({
                "user": u,
                "date": name,
                "title": meta.get("title", ""),
                "body_excerpt": (meta.get("body", "") or "")[:60],
            })
            ck = f"{province}-{city}" if city else province
            cty = city_map.setdefault(ck, {"province": province, "city": city or province, "count": 0, "users": set(), "days": []})
            cty["count"] += 1
            cty["users"].add(u)
            cty["days"].append({
                "user": u,
                "date": name,
                "title": meta.get("title", ""),
                "status": meta.get("status", ""),
                "done": int(meta.get("done", 0) or 0),
                "location": loc,
                "body_excerpt": (meta.get("body", "") or "")[:120],
            })
    def norm_prov(d):
        return {
            "province": d["province"], "count": d["count"],
            "user_count": len(d["users"]), "users": sorted(d["users"]),
            "cities": sorted(d["cities"]),
            "recent_days": sorted(d.get("days", []), key=lambda x: x["date"], reverse=True)[:5],
        }
    def norm_city(d):
        d["days"].sort(key=lambda x: x["date"], reverse=True)
        return {
            "province": d["province"], "city": d["city"],
            "key": f"{d['province']}-{d['city']}",
            "count": d["count"], "user_count": len(d["users"]),
            "users": sorted(d["users"]), "days": d["days"],
        }
    prov_stats = sorted((norm_prov(d) for d in prov_map.values()), key=lambda x: -x["count"])
    city_stats = sorted((norm_city(d) for d in city_map.values()), key=lambda x: -x["count"])
    return jsonify({
        "ok": True,
        "total_logs": total_logs,
        "located_logs": located_logs,
        "province_count": len(prov_stats),
        "city_count": len(city_stats),
        "user_count": len({u for d in city_map.values() for u in d["users"]}),
        "province_stats": prov_stats,
        "city_stats": city_stats,
    })
# ---------------- 周期性总结（月/季/年） ----------------
def load_summaries():
    """读取已生成的总结（monthly/quarterly/yearly -> key -> summary）"""
    if not os.path.exists(SUMMARIES_FILE):
        return {}
    try:
        with open(SUMMARIES_FILE, "r", encoding="utf-8") as fp:
            data = json.load(fp)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}
def save_summaries(summaries):
    """原子写入总结数据"""
    tmp = SUMMARIES_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fp:
        json.dump(summaries, fp, ensure_ascii=False, indent=2)
    os.replace(tmp, SUMMARIES_FILE)
def last_day_of_month(y, m):
    """返回 y 年 m 月的最后一天（date 对象）"""
    if m == 12:
        return date(y, 12, 31)
    return date(y, m + 1, 1) - timedelta(days=1)
def period_end_dates(d):
    """返回 (月最后一天, 季度最后一天, 年最后一天)"""
    month_end = last_day_of_month(d.year, d.month)
    q_first_month = ((d.month - 1) // 3) * 3 + 1
    quarter_end = last_day_of_month(d.year, q_first_month + 2)
    year_end = date(d.year, 12, 31)
    return month_end, quarter_end, year_end
def collect_logs_in_range(start, end):
    """收集 [start, end]（ISO 日期字符串，含边界）内全部用户的日志明细"""
    rows = []
    users = load_users()
    for u in users:
        ud = user_dir(u)
        if not os.path.isdir(ud):
            continue
        for name in sorted(os.listdir(ud)):
            if not (os.path.isdir(os.path.join(ud, name)) and DATE_RE.match(name)):
                continue
            if not (start <= name <= end):
                continue
            meta = read_day(u, name)
            if not meta:
                continue
            rows.append({
                "user": u,
                "date": name,
                "title": meta.get("title", ""),
                "status": meta.get("status", ""),
                "done": int(meta.get("done", 0) or 0),
                "location": meta.get("location", ""),
                "body_excerpt": (meta.get("body", "") or "")[:80],
            })
    rows.sort(key=lambda x: (x["date"], x["user"]))
    return rows
def build_summary(period, year, month=None, quarter=None):
    """生成某周期（month/quarter/year）的总结 dict"""
    if period == "month":
        start = date(year, month, 1)
        end = last_day_of_month(year, month)
        key = f"{year}-{month:02d}"
        label = f"{year}年{month}月"
    elif period == "quarter":
        q_first = (quarter - 1) * 3 + 1
        start = date(year, q_first, 1)
        end = last_day_of_month(year, q_first + 2)
        key = f"{year}-Q{quarter}"
        label = f"{year}年第{quarter}季度"
    else:  # year
        start = date(year, 1, 1)
        end = date(year, 12, 31)
        key = f"{year}"
        label = f"{year}年"
    rows = collect_logs_in_range(start.isoformat(), end.isoformat())
    users = sorted({r["user"] for r in rows})
    prov_set, city_set = set(), set()
    for r in rows:
        loc = (r.get("location") or "").strip()
        if loc and loc not in ("内网/局域网", "无法定位", "未知"):
            p, c = parse_location(loc)
            if p:
                prov_set.add(p)
            if c:
                city_set.add(c)
    return {
        "key": key,
        "label": label,
        "period": period,
        "start": start.isoformat(),
        "end": end.isoformat(),
        "generated_at": now_str(),
        "log_count": len(rows),
        "user_count": len(users),
        "users": users,
        "provinces": sorted(prov_set),
        "cities": sorted(city_set),
        "days": rows[:200],
        "day_truncated": len(rows) > 200,
    }
@app.route("/api/summaries/status")
@login_required
def api_summaries_status():
    """返回当前月/季/年的到期提示状态（是否临近结束、总结是否已生成）"""
    today = date.today()
    month_end, quarter_end, year_end = period_end_dates(today)
    summaries = load_summaries()
    quarter = (today.month - 1) // 3 + 1
    def tip(period, key, label, end):
        return {
            "period": period,
            "key": key,
            "label": label,
            "end": end.isoformat(),
            "due": today >= end - timedelta(days=2),
            "generated": key in summaries.get(period, {}),
        }
    periods = [
        tip("month", f"{today.year}-{today.month:02d}", f"{today.year}年{today.month}月", month_end),
        tip("quarter", f"{today.year}-Q{quarter}", f"{today.year}年第{quarter}季度", quarter_end),
        tip("year", f"{today.year}", f"{today.year}年", year_end),
    ]
    return jsonify({"ok": True, "today": today.isoformat(), "periods": periods})
@app.route("/api/summaries")
@login_required
def api_summaries_list():
    return jsonify({"ok": True, "summaries": load_summaries()})
@app.route("/api/summaries/generate", methods=["POST"])
@login_required
def api_summaries_generate():
    """生成指定周期总结：period=month/quarter/year，month=1-12，quarter=1-4"""
    data = request.get_json(silent=True) or {}
    period = data.get("period", "month")
    year = int(data.get("year") or date.today().year)
    if period not in ("month", "quarter", "year"):
        return jsonify({"ok": False, "msg": "period 无效（month/quarter/year）"}), 400
    if period == "month":
        month = int(data.get("month") or date.today().month)
        if not 1 <= month <= 12:
            return jsonify({"ok": False, "msg": "月份无效"}), 400
        summary = build_summary("month", year, month=month)
    elif period == "quarter":
        quarter = int(data.get("quarter") or ((date.today().month - 1) // 3 + 1))
        if not 1 <= quarter <= 4:
            return jsonify({"ok": False, "msg": "季度无效"}), 400
        summary = build_summary("quarter", year, quarter=quarter)
    else:
        summary = build_summary("year", year)
    summaries = load_summaries()
    summaries.setdefault(period, {})[summary["key"]] = summary
    save_summaries(summaries)
    return jsonify({"ok": True, "summary": summary})
@app.route("/api/summaries/view")
@login_required
def api_summaries_view():
    """查看已生成的总结：period + key（如 2026-09 / 2026-Q3 / 2026）"""
    period = request.args.get("period", "month")
    key = request.args.get("key", "")
    summaries = load_summaries()
    s = summaries.get(period, {}).get(key)
    if not s:
        return jsonify({"ok": False, "msg": "该周期总结尚未生成，请先点击生成"}), 404
    return jsonify({"ok": True, "summary": s})
# ---------------- 启动 ----------------
seed_default_users()
migrate_legacy_logs()
def find_free_port(start=5000, end=5100):
    for p in range(start, end):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(("127.0.0.1", p))
                return p
            except OSError:
                continue
    raise RuntimeError("没有空闲端口")
if __name__ == "__main__":
    import webbrowser
    import threading
    port = find_free_port(5000, 5100)
    url = f"http://127.0.0.1:{port}"
    print(f"[WorkLog] BASE_DIR   = {BASE_DIR}")
    print(f"[WorkLog] USERS_FILE = {USERS_FILE}")
    print(f"[WorkLog] LOG_DIR    = {LOG_DIR}")
    print(f"[WorkLog] IS_FROZEN  = {IS_FROZEN}")
    print(f"[WorkLog] URL        = {url}")
    print("[Important] 如果部署反向代理，请务必配置X‑Real‑IP/X‑Forwarded‑For获取真实客户端IP！")
    if IS_FROZEN:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    app.run(debug=not IS_FROZEN, host="0.0.0.0", port=port, threaded=True)
