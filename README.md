# workLog
> 基于python开发的一个工作日志的dome
## 文件目录
```plaintext
workLog
├─ static
│  ├─ china.json     #中国地理的代码
│  └─ echarts.min.js #echarts代码
├─ templates          #页面目录
│  ├─ admin.html     #管理员页面
│  ├─ index.html     #主界面页面
│  ├─ login.html     #登录页面
│  └─ register.html  #注册页面
├─ app.py             #主程序入口
├─ log.ico            # 软件logo
└─ delete_records.json #删除用户的历史记录

```

## 打包代码
~~~ bash
pyinstaller --onefile --name WorkLog --icon log.ico --collect-all flask --add-data "templates;templates" --add-data "static;static" app.py

>管理员账号：admin
>管理员密码：123456
