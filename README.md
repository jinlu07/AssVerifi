# 舰载机弹药保障作业调度的形式化建模与验证
针对方案正确性验证中存在的弹药保障系统难建模、作业执行行为难描述、形式验证工具难实现等挑战，基于分离逻辑的思想，提出一种弹药保障系统的行为模型，并利用Coq证明辅助工具对作业规划方案进行形式化验证。

对应实际弹药保障作业调度，将弹药保障系统的行为建模为一种两层分离的序列化双层资源堆结构模型。该模型的核心组件是“车资源堆”和“位置资源堆”。并且以此为基础构造了一套可用于描述作业执行行为的建模语言，并给出了其操作语义。通过将该弹药保障模型形式化地实现于Coq证明辅助工具中，工具支持对实际弹药保障作业规划方案的验证。
## 工具中证明系统的构建环节
事实上，我们基于分离逻辑的思想，一个可用于分析和验证弹药保障模型下作业规划方案正确性的交互式Coq证明辅助工具。它涉及到构建语法、定义语义、弹药保障系统计算状态五元组和推理规则等环节。这些环节与工程文件的对应关系如下：
* 构建语法--language.v
* 定义语义--semantic.v
* 弹药保障系统计算状态五元组和推理规则--state.v removestatehv.v SafeinHt.V SafeinSs.v
* 验证实例--方案部署（Asgns1.v）+方案实施（AsgnComps1.v）+资源泄露情形（Asgns2.v Asgns2Abt1.v Asgns2Abt2.v）
此外，还有一些支持工具开发的文件
* 基本引理--Aid.v util.v
* 变量符号--CSSsVerification.v
* 资源互不相等--Neqdefinition.v

工具实现共涉及3357行代码，其中包括95条定义和71条引理。
## 工具开发环境
本工具开发环境为：
* 操作系统：Windows 10
* Coq版本：Coq 8.11.2
## 工具的编译方式
### 1.下载压缩包文件到本地，并解压缩
**注意**：解压缩后的文件路径中，不可以有中文！！
### 2.安装Coq8.11.2并配置环境变量
* 安装Coq
下载地址：https://coq.inria.fr/download

  完成安装后，需要配置Coq的环境变量：
* 打开环境变量设置
![image](./image/hjbl.png)
* 在系统变量的Path一栏中，添加Coq的安装路径
![image](./image/xtbl.jpg)
![image](./image/tjxtbl.jpg)
### 3.在Windows中安装make编译工具
* 安装终端模拟器Cmder（（**需要安装full版本**））

  下载地址：https://cmder.net/

  Cmder解压后即可使用。
* 以**管理员方式**打开Cmder，粘贴如下命令
  *  安装软件管理器Chocolatey

     `@powershell -NoProfile -ExecutionPolicy unrestricted -Command "iex ((new-object net.webclient).DownloadString('https://chocolatey.org/install.ps1'))" && SET PATH=%PATH%;%ALLUSERSPROFILE%\chocolatey\bin`

     **注意**：如果出现`... 未能创建SSL/TLS安全通道 ...`的问题时，可参考如下网站进行解决。 https://blog.csdn.net/qq_43650934/article/details/106637645

  * 安装make编译工具：
    `choco install make`
### 4.安装完成后，重新打开Cmder窗口，进入到解压后的工具文件夹，输入make即可开始编译
![image](./image/make.jpg)

最后直接双击*.v文件，可以用CoqIDE审阅相应代码。


