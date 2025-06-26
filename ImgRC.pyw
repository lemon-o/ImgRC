# -*- coding: utf-8 -*-
from pathlib import Path
import re
import subprocess
import tempfile
import tkinter as tk
from tkinter import filedialog, ttk, messagebox
from urllib.parse import urlparse
import zipfile
from PIL import Image, ImageTk, ImageGrab, ImageDraw
import cv2
import numpy as np
import pyautogui
import time
import threading
import logging
from logging.handlers import RotatingFileHandler
import os
import json
import atexit
from datetime import datetime
import shutil
import keyboard
import ctypes
import sys
import pyperclip
import ttkbootstrap as tb
from ttkbootstrap.constants import *
import ttkbootstrap as ttk
from ttkbootstrap.tooltip import ToolTip
import tkinter.font as tkfont
import requests
from packaging import version
import tkinter.font as tkFont
from ttkbootstrap.widgets import Entry

CURRENT_VERSION = "v1.1.8" #版本号

def run_as_admin():
    if ctypes.windll.shell32.IsUserAnAdmin():
        return  # 已经是管理员，直接运行
    
    messagebox.showinfo("提示", "请以管理员身份启动本程序\n\n1、右键程序图标→【属性】→【兼容性】\n2、勾选【以管理员身份运行此程序】→【确定】")
    sys.exit()

    # # 重新以管理员身份启动
    # exe = sys.executable
    # params = " ".join(sys.argv)
    # ctypes.windll.shell32.ShellExecuteW(None, "runas", exe, params, None, 1)
    # sys.exit()  # 退出当前进程，等待新进程执行

run_as_admin()

def load_icon(icon_name, size=(18, 18)):
    # 构建图标完整路径
    icon_path = os.path.join('icon', icon_name)
    
    try:
        img = Image.open(icon_path).resize(size, Image.Resampling.LANCZOS)
        return ImageTk.PhotoImage(img)
    except FileNotFoundError:
        raise FileNotFoundError(f"图标文件未找到: {icon_path}")
    except Exception as e:
        raise Exception(f"加载图标时出错: {str(e)}")

class ImageRecognitionApp:
    def __init__(self, root):
        self.root = root
        self.root.title("ImgRC")
        self.style = tb.Style(theme='flatly')  # 选择一个主题
        self.image_list = []  # 存储 (图像路径, 步骤名称, 相似度, 键盘动作, 点击位置(F2), 延时ms, 条件, 需跳转，状态， 需禁用， 鼠标动作， 识图区域)
        self.screenshot_area = None  # 用于存储截图区域
        self.rect = None  # 用于存储 Canvas 上的矩形
        self.start_x = None
        self.start_y = None
        self.canvas = None
        self.running = False  # 控制脚本是否在运行
        self.thread = None  # 用于保存线程
        self.hotkey = 'F9'  # 开始/停止热键
        self.screenshot_hotkey = "F8"    # 截图热键
        self.change_coodr_hotkey = "F2"    # 更改点击坐标热键
        self.retake_image_hotkey = "F4"    # 重新截图热键
        self.similarity_threshold = 0.8  # 默认相似度阈值
        self.delay_time = 0.1  # 默认延迟时间
        self.loop_count = 1  # 默认循环次数
        self.retry_count = 0 #重新匹配初始计数
        self.screenshot_folder = 'screenshots'  # 截图保存文件夹
        self.last_used_config = "last_config.json"  # 用于存储最后使用的配置文件名
        self.paused = False  # 控制脚本是否暂停
        self.copied_item = None
        self.config_filename = None  # 默认配置文件名
        self.import_config_filename = None #默认加载配置文件名
        self.start_step_index = 0  # 初始化
        self.current_loop = 0 #初始化
        self.default_photo = None  # 初始化
        self.current_step_name = None # 初始化
        self.from_step = False
        self.need_retake_screenshot = False
        self.import_and_load = False
        self.config_loaded = False
        self.is_cut_mode = False # 用来标记当前操作是剪切而非普通复制
        self.is_dragging = False
        self.rc_area_change = False
        self.step_on_search = False
        self.rc_area_dialog = False
        self.last_area_choice = 'screenshot'

        self.checking_update = False
        self.downloading = False
        self.latest_version = ""
        self.update_available = False
        self.download_url = ""
        self.update_window = None
        self.progress_bar = None
        self.status_label = None
        self.update_button = None
        self.cancel_button = None
        self.button_frame = None

        self.cut_original_indices = []  # 存放被剪切条目的原始索引
        self.copied_items = []
        self.screen_scale = 1
        self.follow_current_step = tk.BooleanVar(value=False)  # 控制是否跟随当前步骤
        self.only_keyboard_var = tk.BooleanVar(value=False)  # 控制是否只进行键盘操作
        # 先隐藏窗口
        root.withdraw()
        self.init_ui()
        # 自动调整窗口大小并居中
        self.adjust_window()
        # 设置窗口图标（相对路径）
        root.iconbitmap("icon/app.ico") 
        self.root.resizable(False, False)  # 禁止调整窗口大小
        root.deiconify()  # 显示窗口  
        self.tree.image_refs = []  # 初始化 image_refs 属性
        self.init_logging()
        self.bind_arrow_keys()
        self.create_context_menu()
        atexit.register(self.cleanup_on_exit)
        self.hotkey_id = None # 初始化热键id
        self.register_global_hotkey() # 注册全局热键  
        self.load_last_used_config() #加载上次的配置文件

    def init_ui(self):
        # 主框架布局
        self.main_frame = tb.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # 区域L：包含区域A（按钮区域）和区域B（树形区域）垂直排列
        self.region_l = tb.Frame(self.main_frame)
        self.region_l.pack(side=tk.LEFT, fill=tk.BOTH, expand=False, padx=5, pady=5)

        # 区域A：按钮区域
        self.region_a = tb.Frame(self.region_l, height=100)  # 设置Frame的高度为100
        self.region_a.pack(fill=tk.BOTH, padx=2, pady=0)

        # 图标缓存
        self.icons = {
            "export": load_icon("export.png"),
            "import": load_icon("import.png"),
            "save": load_icon("save.png"),
            "load": load_icon("load.png"),
            "add": load_icon("add.png"),
        }

        self.hover_icons = {
            "export": load_icon("export_hover.png"),
            "import": load_icon("import_hover.png"),
            "save": load_icon("save_hover.png"),
            "load": load_icon("load_hover.png"),
            "add": load_icon("add_hover.png"),
        }

        # 定义鼠标进入和离开的回调函数
        def on_enter(event, button, hover_icon):
            button.config(image=hover_icon)

        def on_leave(event, button, normal_icon):
            button.config(image=normal_icon)

        # 在 region_a 中创建带边框的容器
        self.bordered_frame = tk.Frame(self.region_a)
        self.bordered_frame.pack(fill=tk.BOTH, padx=0, pady=0)

        def on_region_a_enter(event):
            if self.follow_current_step.get() and not self.rc_area_dialog:
                # 鼠标进入 region_a，取消置顶
                self.root.attributes('-topmost', False)

        def on_region_a_leave(event):
            if not self.follow_current_step.get() and not self.rc_area_dialog:
                return

            # region_a 的全局坐标和尺寸
            x0 = self.region_a.winfo_rootx()
            y0 = self.region_a.winfo_rooty()
            x1 = x0 + self.region_a.winfo_width()
            y1 = y0 + self.region_a.winfo_height()

            # 鼠标当前全局坐标
            mx, my = event.x_root, event.y_root

            # 只有当鼠标真地跑到 region_a 的外面，才恢复置顶
            if not (x0 <= mx <= x1 and y0 <= my <= y1):
                self.root.attributes('-topmost', True)

        # 绑定事件
        self.region_a.bind("<Enter>", on_region_a_enter)
        self.region_a.bind("<Leave>", on_region_a_leave)

        # 配置按钮行
        self.config_button_frame = ttk.Frame(self.bordered_frame)
        self.config_button_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 10))

        # 导出配置按钮
        self.Export_config_button = ttk.Button(
            self.config_button_frame, 
            image=self.icons["export"],
            command=self.export_config, 
            bootstyle="primary-outline"
        )
        self.Export_config_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        ToolTip(self.Export_config_button, "导出配置")
        self.Export_config_button.bind(
            "<Enter>",
            lambda e: on_enter(e, self.Export_config_button, self.hover_icons["export"]), add="+"    
        )
        self.Export_config_button.bind(
            "<Leave>",
            lambda e: on_leave(e, self.Export_config_button, self.icons["export"]), add="+"       
        )

        # 导入配置按钮
        self.Import_config_button = ttk.Button(
            self.config_button_frame, 
            image=self.icons["import"],
            command=self.import_config, 
            bootstyle="primary-outline"
        )
        self.Import_config_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        ToolTip(self.Import_config_button, "导入配置")
        self.Import_config_button.bind(
            "<Enter>", 
            lambda e: on_enter(e, self.Import_config_button, self.hover_icons["import"]), add="+"  
        )
        self.Import_config_button.bind(
            "<Leave>", 
            lambda e: on_leave(e, self.Import_config_button, self.icons["import"]), add="+"  
        )

        # 保存配置按钮
        self.save_config_button = ttk.Button(
            self.config_button_frame, 
            image=self.icons["save"],
            command=self.save_config, 
            bootstyle="primary-outline"
        )
        self.save_config_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        ToolTip(self.save_config_button, "保存配置")
        self.save_config_button.bind(
            "<Enter>", 
            lambda e: on_enter(e, self.save_config_button, self.hover_icons["save"]), add="+"  
        )
        self.save_config_button.bind(
            "<Leave>", 
            lambda e: on_leave(e, self.save_config_button, self.icons["save"]), add="+"  
        )

        # 加载配置按钮
        self.load_config_button = ttk.Button(
            self.config_button_frame, 
            image=self.icons["load"],
            command=self.load_config, 
            bootstyle="primary-outline"
        )
        self.load_config_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))
        ToolTip(self.load_config_button, "加载配置")
        self.load_config_button.bind(
            "<Enter>", 
            lambda e: on_enter(e, self.load_config_button, self.hover_icons["load"]), add="+"  
        )
        self.load_config_button.bind(
            "<Leave>", 
            lambda e: on_leave(e, self.load_config_button, self.icons["load"]), add="+"  
        )

        # 操作按钮行
        self.top_button_frame = tb.Frame(self.bordered_frame)
        self.top_button_frame.pack(fill=tk.BOTH, expand=True, pady=(2, 10))

        # 截取图片按钮
        self.screenshot_button = tb.Button(
            self.top_button_frame, 
            image=self.icons["add"],
            command=self.prepare_capture_screenshot, 
            bootstyle="primary-outline"
        )
        self.screenshot_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        ToolTip(self.screenshot_button, "截取图片以添加步骤(F8)")
        self.screenshot_button.bind(
            "<Enter>",
            lambda e: on_enter(e, self.screenshot_button, self.hover_icons["add"]), add="+"    
        )
        self.screenshot_button.bind(
            "<Leave>",
            lambda e: on_leave(e, self.screenshot_button, self.icons["add"]), add="+"       
        )

        # 运行/停止脚本按钮
        self.toggle_run_button = tb.Button(
            self.top_button_frame, 
            text="开始运行(F9)", 
            command=self.toggle_script, 
            bootstyle="primary-outline"
        )
        self.toggle_run_button.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)

        # 循环次数输入框
        self.loop_count_entry = tb.Entry(self.top_button_frame, width=3)
        self.loop_count_entry.insert(0, str(self.loop_count))
        self.loop_count_entry.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=0)
        self.loop_count_label = tb.Label(self.top_button_frame, text="次")
        self.loop_count_label.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=0)

        # 区域M：勾选框区域
        self.region_m = tb.Frame(self.region_l)
        self.region_m.pack(fill=tk.X, padx=2, pady=0)

        # 默认运行中隐藏
        self.allow_minimize_var = tk.BooleanVar(value=True)
        self.follow_current_step = tk.BooleanVar(value=False)

        # 运行中隐藏勾选框
        self.allow_minimize_checkbox = tb.Checkbutton(
            self.region_m, 
            text="运行时隐藏", 
            variable=self.allow_minimize_var, 
            bootstyle="toolbutton",
            command=self.toggle_allow_minimize
        )
        self.allow_minimize_checkbox.pack(side=tk.LEFT, expand=True, fill=tk.X, pady=5)

        # 窗口置顶
        self.follow_step_checkbox = tb.Checkbutton(
            self.region_m, 
            text="窗口置顶", 
            variable=self.follow_current_step, 
            bootstyle="toolbutton",
            command=self.toggle_topmost
        )
        self.follow_step_checkbox.pack(side=tk.LEFT, expand=True, fill=tk.X, pady=5)

        # 仅键盘操作勾选框
        # self.only_keyboard_checkbox = tb.Checkbutton(self.region_m, text="仅键盘操作", variable=self.only_keyboard_var, bootstyle=TOOLBUTTON)
        # self.only_keyboard_checkbox.pack(side=tk.LEFT, pady=5)

        style = tb.Style()  
        style.configure("Border.TFrame", background="#ced4da")
        style.configure("InnerR.TFrame", background="white")
        border_width = 1

        # 区域S：搜索框区域
        self.region_s = tb.Frame(self.region_l)
        self.region_s.pack(fill=tk.X, padx=2, pady=0)

        # 外层 Frame 模拟边框
        search_border = tb.Frame(self.region_s)
        search_border.pack(fill=tk.X, expand=True, padx=0, pady=5)
        search_border.configure(style="Border.TFrame")

        # 内层 Frame 白底（必须使用 bootstyle="light"）
        search_inner = tb.Frame(
            search_border, 
            bootstyle="light",
            style="InnerR.TFrame"
        )
        search_inner.pack(fill=tk.X, expand=True, padx=border_width, pady=border_width)

        search_var = tk.StringVar()
        # 定义所有状态下的边框颜色为白色
        style.map(
            'White.TEntry',
            bordercolor=[
                ('active', 'white'),    # 鼠标悬停/激活状态
                ('focus', 'white'),     # 获取焦点状态
                ('disabled', 'white'),  # 禁用状态
                ('!disabled', 'white')  # 默认状态
            ],
            lightcolor=[('', 'white')],  # 未选中时的边框高亮
            darkcolor=[('', 'white')]    # 阴影颜色
        )
        # 配置基础样式
        style.configure(
            'White.TEntry',
            foreground='black',          # 文字颜色
            fieldbackground='white',     # 背景色
            borderwidth=1               # 边框宽度
        )
        # 创建并应用 Entry
        search_var = tk.StringVar()
        entry = Entry(
            search_inner,
            textvariable=search_var,
            style='White.TEntry',
        )
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 0), pady=0)

        # 图标
        img = Image.open("icon/search.png").resize((16, 16), Image.Resampling.LANCZOS)
        search_icon = ImageTk.PhotoImage(img)

        icon_label = tk.Label(search_inner, image=search_icon, bg="white", bd=0)
        icon_label.image = search_icon  # 防止被垃圾回收
        icon_label.pack(side=tk.RIGHT, padx=5)

        placeholder_original = "在步骤名称中搜索"
        placeholder = f"{placeholder_original}"  # 统一使用这个变量

        def set_placeholder():
            entry.delete(0, tk.END)
            entry.insert(0, placeholder)
            entry.config(foreground='grey')

        def clear_placeholder(event=None):
            if entry.get() == placeholder:
                entry.delete(0, tk.END)
                entry.config(foreground='black')

        def restore_placeholder(event=None):
            if not entry.get():
                set_placeholder()
                
        def on_search(*args):
            text = search_var.get().strip()
            if text == "" or text == placeholder_original:
                self.step_on_search = True
                self.update_image_listbox("")  # 显示所有
            else:
                self.step_on_search = True
                self.update_image_listbox(text)

        # 初始化 placeholder
        set_placeholder()

        # 事件绑定
        entry.bind("<FocusIn>", clear_placeholder)
        entry.bind("<FocusOut>", restore_placeholder)
        search_var.trace_add('write', on_search)

        # 区域B：树形区域
        self.region_b = tb.Frame(self.region_l)
        self.region_b.pack(fill=tk.BOTH, expand=True, padx=2, pady=5)

        # 使用 Treeview 来显示图片和延时ms
        self.tree = ttk.Treeview(self.region_b, columns=(
            "图片名称", "步骤名称", "相似度", "键盘动作", "点击位置(F2)", "延时ms", "条件", 
            "需跳转", "状态", "需禁用", "鼠标动作", "条件2", "需跳转2", "需禁用2", "识图区域"
        ), show='headings')#新增索引
        self.tree.heading("图片名称", text="图片名称")
        self.tree.heading("步骤名称", text="步骤名称")
        self.tree.heading("相似度", text="相似度")
        self.tree.heading("键盘动作", text="键盘动作")
        self.tree.heading("点击位置(F2)", text="点击位置(F2)")
        self.tree.heading("延时ms", text="延时ms")
        self.tree.heading("条件", text="条件")
        self.tree.heading("需跳转", text="需跳转")
        self.tree.heading("状态", text="状态")
        self.tree.heading("需禁用", text="需禁用")
        self.tree.heading("鼠标动作", text="鼠标动作")
        self.tree.heading("条件2", text="条件2")
        self.tree.heading("需跳转2", text="需跳转2")
        self.tree.heading("需禁用2", text="需禁用2")
        self.tree.heading("识图区域", text="识图区域")
        #新增索引

        # 设置列宽和对齐方式（居中）
        self.tree.column("图片名称", width=75, anchor='center')
        self.tree.column("步骤名称", width=75, anchor='center')
        self.tree.column("相似度", width=75, anchor='center')
        self.tree.column("键盘动作", width=75, anchor='center')
        self.tree.column("点击位置(F2)", width=75, anchor='center')
        self.tree.column("延时ms", width=75, anchor='center')
        self.tree.column("条件", width=20, anchor='center')
        self.tree.column("需跳转", width=75, anchor='center')
        self.tree.column("状态", width=75, anchor='center')
        self.tree.column("需禁用", width=75, anchor='center')
        self.tree.column("鼠标动作", width=75, anchor='center')
        self.tree.column("条件2", width=75, anchor='center')
        self.tree.column("需跳转2", width=75, anchor='center')
        self.tree.column("需禁用2", width=75, anchor='center')
        self.tree.column("识图区域", width=75, anchor='center')
        #新增索引

        # 1. 在 Treeview 上配置一个 hover 标签的样式
        self.tree.tag_configure('hover', background="#f3f3f3")  

        # 2. 用来记录上一次悬停的行
        self._prev_hover_row = None

        def add_hover(row_id):
            if row_id and self.tree.exists(row_id):
                # 取出已有所有标签
                tags = list(self.tree.item(row_id, "tags"))

                # 如果还没有 hover，就追加
                if "hover" not in tags:
                    tags.append("hover")
                    self.tree.item(row_id, tags=tuple(tags))

        def remove_hover(row_id):
            if row_id and self.tree.exists(row_id):
                tags = list(self.tree.item(row_id, "tags"))
                if "hover" in tags:
                    tags.remove("hover")
                    self.tree.item(row_id, tags=tuple(tags))

        def on_motion(event):
            row_id = self.tree.identify_row(event.y)
            if row_id != self._prev_hover_row:
                remove_hover(self._prev_hover_row)   # 只拿掉 hover，不碰其他标签
                add_hover(row_id)                    # 只加 hover，不覆盖其他标签
                self._prev_hover_row = row_id

        def on_leave2(event):
            remove_hover(self._prev_hover_row)
            self._prev_hover_row = None

        self.tree.bind('<Motion>', on_motion)
        self.tree.bind('<Leave>', on_leave2)

        #显示的列
        self.tree.configure(displaycolumns=["步骤名称", "延时ms"])
        #禁用状态的颜色
        self.tree.tag_configure("disabled", foreground="#ced4da")

        # 将 Treeview 添加到区域B
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # 创建垂直滚动条，并固定在 Treeview 右侧
        self.scrollbar = ttk.Scrollbar(self.region_b, orient="vertical", command=self.tree.yview)
        self.scrollbar.pack(side=tk.LEFT, fill=tk.Y)  # 让滚动条紧贴 Treeview

        # 配置 Treeview 使用滚动条
        self.tree.configure(yscrollcommand=self.scrollbar.set)

        # 创建外部边框区域（使用指定灰色）
        self.region_r_border = tb.Frame(self.main_frame)
        self.region_r_border.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=7, pady=10)

        # 内部区域R设置白色背景
        self.region_r = tb.Frame(
            self.region_r_border, 
            bootstyle="light",
            style="InnerR.TFrame"
        )
        self.region_r.pack(fill=tk.BOTH, expand=True, padx=1, pady=1)

        # 配置自定义样式
        style = tb.Style()
        style.configure("Border.TFrame", background="#ced4da")
        style.configure("InnerR.TFrame", background="white")
        style.configure("PreviewBg.TFrame", background="#f8f9fa")
        style.configure("ImageContainer.TFrame", background="#f8f9fa")
        self.region_r_border.configure(style="Border.TFrame")

        # 区域C：图片预览区域（取消底部边距）
        self.region_c = tb.Frame(self.region_r, style="PreviewBg.TFrame")
        self.region_c.pack(fill=tk.BOTH, padx=0, pady=(0, 0), expand=True) 

        # 获取屏幕宽度并计算 1/5
        screen_width = self.root.winfo_screenwidth()  # 获取整个屏幕的宽度
        target_width = int(screen_width / 7)  
        target_height = int(target_width * 37 / 50)  # 保持宽高比

        # 预览面板
        self.preview_panel = tb.Frame(
            self.region_c,
            width=target_width,
            height=target_height
        )
        self.preview_panel.pack_propagate(False)
        self.preview_panel.pack()

        # 图像容器
        self.preview_container = tb.Frame(
            self.preview_panel,
            width=target_width, 
            height=target_height,
            style="ImageContainer.TFrame"
        )
        self.preview_container.pack_propagate(False)
        self.preview_container.pack(pady=0, padx=0)

        self.preview_image_label = tb.Label(
            self.preview_container,
            bootstyle=SECONDARY,
            anchor="center",
            background="#f8f9fa"
        )
        self.preview_image_label.pack(fill=tk.BOTH, expand=True)
        self.load_default_image()# 加载默认图片

        # 区域D：紧贴区域C（取消顶部边距）
        self.region_d = tb.Frame(self.region_r, style="InnerR.TFrame")
        self.region_d.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))  

        def on_region_d_enter(event):
            if self.follow_current_step.get() and not self.rc_area_dialog:
                # 鼠标进入 region_d，取消置顶
                self.root.attributes('-topmost', False)

        def on_region_d_leave(event):
            if self.follow_current_step.get() and not self.rc_area_dialog:
                # 鼠标离开 region_d，恢复置顶
                self.root.attributes('-topmost', True)

        # 绑定事件
        self.region_d.bind("<Enter>", on_region_d_enter)
        self.region_d.bind("<Leave>", on_region_d_leave)

        # 详细信息标签区域
        # —— 第一行：标题 + 文件名 —— #
        self.label_frame = tk.Frame(self.region_d)
        self.label_frame.pack(fill="x",padx=10, pady=(20, 0))

        # 标题“详细信息”
        # 获取默认字体，并克隆一个出来
        default_font = tkfont.nametofont("TkDefaultFont").copy()
        default_font.configure(weight="bold")  # 设置为加粗

        # 应用到 label 上
        self.label_title = tk.Label(
            self.label_frame,
            text="详细信息",
            anchor="w",
            foreground="#495057",
            font=default_font
        )
        self.label_title.pack(side="left")

        # 文件名
        self.label_filename = tk.Label(
            self.label_frame,
            text="",          # 会在 update 时填充
            anchor="w",
            foreground="#9D9FA1"
        )
        self.label_filename.pack(side="right")

        # —— 第二行：各字段标签 —— #
        self.labels_frame = tk.Frame(self.region_d)
        self.labels_frame.pack(fill="x", pady=(2, 0))

        # 初始化字段标签
        self.labels = {}         # 右侧：字段值 Label
        self.label_titles = {}   # ✅ 左侧：字段名 Label

        字段名列表 = ["图片名称", "识图区域", "条件判断", "相似度", "点击位置(F2)", "键盘动作", "鼠标动作", "状态"]

        for name in 字段名列表:
            row_frame = tk.Frame(self.labels_frame)
            row_frame.pack(fill="x", padx=10, pady=0)

            label_left = tk.Label(
                row_frame,
                text=f"{name}:",
                anchor="w",
                width=10,
            )
            label_left.pack(side="left")

            label_right = tk.Label(
                row_frame,
                text="",
                anchor="e",
                justify="right",
            )
            label_right.pack(side="right", fill="x", expand=True)

            self.label_titles[name] = label_left  # ✅ 保存左边 Label
            self.labels[name] = label_right       # ✅ 保存右边 Label

        for lbl in self.labels.values():
            lbl.configure(foreground="#495057")

        for lbl in self.label_titles.values():
            lbl.configure(foreground="#495057")
         
        # 绑定焦点事件
        self.tree.bind("<FocusIn>", self.update_label)

        # 初始化上下文菜单
        self.tree.unbind('<Double-1>')
        self.tree.unbind('<Double-3>')
        self.tree.unbind('<Double-2>')

        # 为上下文菜单添加此绑定
        self.tree.bind('<Button-3>', self.show_context_menu)  # 右键点击
        self.tree.bind('<Button-1>', self.on_treeview_select)  # 左键点击
        # 绑定双击事件
        self.tree.bind('<Double-Button-1>', self.on_treeview_double_click)

        # 在 Treeview 创建后添加选择事件绑定
        self.tree.bind('<<TreeviewSelect>>', self.on_treeview_select)
        self.image_dict = {}  # 存储 Treeview 行的图片

        # 绑定鼠标拖动事件
        self.tree.bind("<ButtonPress-1>", self.on_treeview_drag_start)
        self.tree.bind("<B1-Motion>", self.on_treeview_drag_motion)
        self.tree.bind("<ButtonRelease-1>", self.on_treeview_drag_release)

    def adjust_window(self):
        """
        自动调整窗口大小并居中
        基于update_idletasks()+winfo_reqwidth()/winfo_reqheight()
        """
        # 更新窗口计算布局
        self.root.update_idletasks()
        
        # 获取窗口内容所需的最小尺寸
        req_width = self.root.winfo_reqwidth()
        req_height = self.root.winfo_reqheight()
        
        # 获取屏幕尺寸
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 计算居中位置
        x = (screen_width - req_width) // 2
        y = (screen_height - req_height) // 2
        
        # 设置窗口大小和位置
        self.root.geometry(f"{req_width}x{req_height}+{x}+{y}")
        
    # 获取屏幕缩放比例
    def get_screen_scale(self):
        try:
            user32 = ctypes.windll.user32
            dpi = user32.GetDpiForSystem()  # 获取DPI
            self.screen_scale = dpi / 96 # 屏幕缩放比例
        except Exception as e:
            print(f"获取屏幕缩放比例失败: {e}")
            self.screen_scale = 1

    def load_last_used_config(self):
        """尝试加载最后使用的配置文件"""
        global selected_config
        try:
            # 检查是否有记录的最后使用的配置文件
            if os.path.exists(self.last_used_config):
                with open(self.last_used_config, 'r', encoding='utf-8') as f:
                    last_config = json.load(f)
                    if 'config_file' in last_config:
                        selected_config = last_config['config_file']
                        self.load_selected_config()
        except Exception as e:
            print(f"加载最后配置记录失败: {e}")
        return False

    def save_last_used_config(self, config_file):
        """保存最后使用的配置文件名"""
        try:
            with open(self.last_used_config, 'w', encoding='utf-8') as f:
                json.dump({'config_file': config_file}, f)
        except Exception as e:
            print(f"保存最后配置记录失败: {e}")

    def load_default_image(self):
        try:
            # 获取当前工作目录中的默认图像路径
            working_dir = os.getcwd()
            default_image_path = os.path.join(working_dir, "icon", "default_img.png")

            if not os.path.exists(default_image_path):
                print("默认图片路径不存在:", default_image_path)
                return

            original_image = Image.open(default_image_path)

            def _update_when_ready():
                w = self.preview_container.winfo_width()
                h = self.preview_container.winfo_height()

                if w < 10 or h < 10:
                    self.preview_container.after(100, _update_when_ready)
                    return

                original_w, original_h = original_image.size

                # 计算缩放比例：宽或高不足就放大，不允许超过容器
                width_ratio = w / original_w
                height_ratio = h / original_h

                scale_ratio = max(width_ratio, height_ratio)
                new_w = int(original_w * scale_ratio)
                new_h = int(original_h * scale_ratio)

                # 限制最终大小不超过容器
                if new_w > w or new_h > h:
                    limit_ratio = min(w / new_w, h / new_h)
                    new_w = int(new_w * limit_ratio)
                    new_h = int(new_h * limit_ratio)

                resized_image = original_image.resize((new_w, new_h), Image.Resampling.LANCZOS)

                self.default_photo = ImageTk.PhotoImage(resized_image)
                self.preview_image_label.config(image=self.default_photo)
                self.preview_image_label.image = self.default_photo

            self.preview_container.after(100, _update_when_ready)

        except Exception as e:
            print("加载默认图片失败:", e)

    def toggle_allow_minimize(self):
        if self.allow_minimize_var.get():
            # 如果勾选“运行时隐藏”，取消勾选“窗口置顶”
            self.follow_current_step.set(False)
            self.root.attributes('-topmost', False)  # 取消窗口置顶
        else:
            # 如果“运行时隐藏”未勾选，检查“窗口置顶”的状态
            if not self.follow_current_step.get():
                self.root.attributes('-topmost', False)

    def toggle_topmost(self):
        if self.follow_current_step.get():
            # 如果勾选“窗口置顶”，取消勾选“运行时隐藏”
            self.allow_minimize_var.set(False)
            self.root.attributes('-topmost', True)  # 设置窗口置顶
        else:
            # 如果“窗口置顶”未勾选，取消窗口置顶状态
            self.root.attributes('-topmost', False)

    def init_logging(self):  # 初始化日志
        handler = RotatingFileHandler(
            'app.log', 
            maxBytes=5*1024*1024,  # 最大5MB
            backupCount=1          # 只保留 1 个备份
        )
        logging.basicConfig(
            handlers=[handler],
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s'
        )

    #以下是检测更新的函数
    def check_update(self):
        """通过菜单按钮触发的更新检查"""
        if self.checking_update or self.downloading:
            return
            
        self.checking_update = True
        try:
            self._create_update_window("正在检查更新...", show_progress=False)
            
            update_thread = threading.Thread(
                target=self._check_update_background,
                daemon=True
            )
            update_thread.start()
            
        except Exception as e:
            self.checking_update = False
            messagebox.showerror("错误", f"启动更新检查失败: {str(e)}")
            if self.update_window and self.update_window.winfo_exists():
                self.update_window.destroy()

    def _create_update_window(self, message, show_progress=False):
        """创建/更新共用窗口"""
        try:
            # 如果窗口不存在，则先创建
            if self.update_window is None or not self.update_window.winfo_exists():
                # 创建新窗口并暂时隐藏
                self.update_window = tk.Toplevel(self.root)
                self.update_window.withdraw()
                self.update_window.title("检查更新")
                self.update_window.transient(self.root)
                self.update_window.grab_set()
                
                # 先让根窗口计算完毕，以获取最新的尺寸
                self.root.update_idletasks()
                main_w = self.root.winfo_width()
                main_h = self.root.winfo_height()
                
                # 根据根窗口尺寸，计算更新窗口的大小
                new_w = int(main_w * 329 / 669)
                new_h = int(main_h * 160 / 544)
                
                # 计算承载状态标签的容器宽高
                container_w = int(new_w * 180 / 203)
                container_h = int(new_h * 100 / 399)
                
                # -------------------- 标题 Label --------------------
                self.title_label = ttk.Label(
                    self.update_window,
                    text="软件更新",
                    font=('Microsoft YaHei', 12, 'bold')
                )
                self.title_label.pack(pady=(10, 5))
                
                # -------------------- 状态容器 --------------------
                self.status_frame = ttk.Frame(
                    self.update_window,
                    width=container_w,
                    height=container_h
                )
                self.status_frame.pack_propagate(False)
                self.status_frame.pack(pady=(0, 10))
                
                # 状态标签
                self.status_label = ttk.Label(
                    self.status_frame,
                    text=message,
                    font=('Microsoft YaHei', 10)
                )
                self.status_label.pack(expand=True)
                
                # -------------------- 进度条 --------------------
                self.progress_bar = ttk.Progressbar(
                    self.update_window,
                    orient="horizontal",
                    length=container_w,
                    mode="determinate"
                )
                
                # -------------------- 按钮容器 --------------------
                self.button_frame = ttk.Frame(self.update_window)
                self.button_frame.pack(pady=10)
                
                # 更新按钮
                self.update_button = ttk.Button(
                    self.button_frame,
                    text="更新",
                    command=self._safe_start_download,
                    bootstyle="primary-outline"
                )
                self.update_button.pack(side="left", padx=10)
                
                # 取消按钮
                self.cancel_button = ttk.Button(
                    self.button_frame,
                    text="取消",
                    command=self._safe_cancel_update,
                    bootstyle="primary-outline"
                )
                self.cancel_button.pack(side="left", padx=10)
                
                # 窗口关闭事件
                self.update_window.protocol("WM_DELETE_WINDOW", self._safe_cancel_update)
                
                # 设置图标
                self.update_window.iconbitmap("icon/app.ico")
                
                # 设置窗口位置
                main_x = self.root.winfo_x()
                main_y = self.root.winfo_y()
                x = main_x + (main_w - new_w) // 2
                y = main_y + (main_h - new_h) // 2
                self.update_window.geometry(f"{new_w}x{new_h}+{x}+{y}")
                
                # 显示窗口
                self.update_window.deiconify()
            
            else:
                # 更新状态文字
                self.status_label.config(text=message)
            
            # 根据参数决定显示内容
            if show_progress:
                # 立即删除按钮并显示进度条
                self._remove_buttons()
                self.progress_bar.pack(pady=5)
                self.progress_bar['value'] = 0
            else:
                # 确保按钮可见
                self.button_frame.pack(pady=10)
                self.progress_bar.pack_forget()
                
                # 更新按钮状态
                if hasattr(self, 'update_available'):
                    state = "normal" if self.update_available else "disabled"
                    self.update_button.config(state=state)
        
            # 强制布局更新
            self.update_window.update_idletasks()

        except Exception as e:
            messagebox.showerror("窗口创建错误", f"创建更新窗口失败: {str(e)}")

    def _remove_buttons(self):
        """永久删除按钮组件"""
        try:
            if hasattr(self, 'button_frame') and self.button_frame.winfo_exists():
                # 销毁按钮框架及其所有子组件
                self.button_frame.destroy()
                
                # 删除相关属性（可选，如果不打算重新创建按钮）
                del self.button_frame
                del self.update_button
                del self.cancel_button
                
        except Exception as e:
            messagebox.showerror("错误", f"删除按钮失败: {str(e)}")

    def _safe_start_download(self):
        """安全启动下载，处理可能的异常"""
        try:
            self._start_download()
        except Exception as e:
            messagebox.showerror("错误", f"启动下载失败: {str(e)}")
            if self.update_window and self.update_window.winfo_exists():
                self.update_window.destroy()

    def _safe_cancel_update(self):
        """安全取消更新，处理可能的异常"""
        try:
            self._cancel_update()
        except Exception as e:
            messagebox.showerror("错误", f"取消操作失败: {str(e)}")


    def _cancel_update(self):
        """取消更新操作"""
        self.checking_update = False
        self.downloading = False
        if self.update_window and self.update_window.winfo_exists():
            self.update_window.destroy()
        self.update_window = None

    def _check_update_background(self):
        """后台检查更新逻辑"""
        try:
            response = requests.get(
                "https://api.github.com/repos/lemon-o/ImgRC/releases/latest",
                timeout=10
            )
            response.raise_for_status()
            
            latest_release = response.json()
            self.latest_version = latest_release['tag_name']
            self.download_url = self._find_windows_installer(latest_release.get('assets', []))
            
            if not self.download_url:
                raise Exception("未找到Windows安装程序")
            
            current = version.parse(CURRENT_VERSION.lstrip('v'))
            latest = version.parse(self.latest_version.lstrip('v'))
            
            if latest > current:
                self.update_available = True
                self.root.after(0, self._show_update_available)
            else:
                self.update_available = False
                self.root.after(0, self._show_no_update)
                
        except requests.RequestException as e:
            self.root.after(0, lambda: self._show_update_error(f"网络错误: {str(e)}"))
        except Exception as e:
            self.root.after(0, lambda: self._show_update_error(f"检查更新失败: {str(e)}"))
        finally:
            self.checking_update = False

    def _find_windows_installer(self, assets):
        """查找Windows安装程序"""
        for asset in assets:
            if asset['name'].endswith('.exe') and "setup" in asset['name'].lower():
                return asset['browser_download_url']
        for asset in assets:
            if asset['name'].endswith('.msi'):
                return asset['browser_download_url']
        return ""

    def _show_update_available(self):
        """显示更新可用"""
        try:
            self._create_update_window(
                f"发现新版本 {self.latest_version}，当前版本: {CURRENT_VERSION}",
                show_progress=False
            )
            if self.update_button:
                self.update_button.config(state="normal")
        except Exception as e:
            messagebox.showerror("错误", f"显示更新信息失败: {str(e)}")

    def _show_no_update(self):
        """显示已是最新版本"""
        try:
            self._create_update_window(
                f"当前已是最新版本 ({CURRENT_VERSION})",
                show_progress=False
            )
            if self.update_button:
                self.update_button.config(state="disabled")
        except Exception as e:
            messagebox.showerror("错误", f"显示版本信息失败: {str(e)}")

    def _show_update_error(self, message):
        """显示更新错误"""
        try:
            self._create_update_window(
                f"更新检查失败: {message}",
                show_progress=False
            )
            if self.update_button:
                self.update_button.config(state="disabled")
            self.root.after(3000, self._cancel_update)
        except Exception as e:
            messagebox.showerror("错误", f"显示错误信息失败: {str(e)}")

    def _start_download(self):
        """开始下载更新"""
        if not self.download_url:
            messagebox.showerror("错误", "无法获取下载链接")
            self._cancel_update()
            return
            
        self.downloading = True
        try:
            self._create_update_window(
                f"正在下载 {self.latest_version}...",
                show_progress=True
            )
            
            download_thread = threading.Thread(
                target=self._download_and_install,
                daemon=True
            )
            download_thread.start()
        except Exception as e:
            self.downloading = False
            messagebox.showerror("错误", f"启动下载失败: {str(e)}")
            self._cancel_update()

    def format_speed(self, speed_bps):
        """
        将字节每秒 (B/s) 转换为字符串，自动选择 B/s、KB/s、MB/s 单位
        例如：123 字节/秒 → "123.00 B/s"
             4096 字节/秒 → "4.00 KB/s"
             5*1024*1024 字节/秒 → "5.00 MB/s"
        """
        if speed_bps >= 1024 * 1024:
            return f"{speed_bps / (1024 * 1024):.2f} MB/s"
        elif speed_bps >= 1024:
            return f"{speed_bps / 1024:.2f} KB/s"
        else:
            return f"{speed_bps:.2f} B/s"

    def _download_and_install(self):
        """下载并安装更新"""
        try:
            # 获取文件名
            parsed_url = urlparse(self.download_url)
            filename = os.path.basename(parsed_url.path)
            temp_dir = os.environ.get('TEMP', os.getcwd())
            download_path = os.path.join(temp_dir, filename)
            
            # 添加下载信息标签（单行显示）
            self.root.after(0, self._add_download_info_labels)
            
            # 标记正在下载
            self.downloading = True
            
            # 初始化速度计算相关变量
            start_time = time.time()
            self._last_update_time = start_time
            self._last_size = 0
            self._speed_history = []  # 存储最近 3 次的瞬时速度（B/s）
            
            downloaded = 0
            
            with requests.get(self.download_url, stream=True, timeout=30) as r:
                r.raise_for_status()
                total_size = int(r.headers.get('content-length', 0))
                
                # 开始写入文件
                with open(download_path, 'wb') as f:
                    for chunk in r.iter_content(chunk_size=8192):
                        if not self.downloading:
                            # 如果中途取消下载，则删除临时文件并返回
                            if os.path.exists(download_path):
                                os.remove(download_path)
                            return
                        
                        if chunk:
                            f.write(chunk)
                            downloaded += len(chunk)
                            
                            # 当前时间
                            current_time = time.time()
                            # 如果距离上次更新时间超过 0.1 秒，则计算速度并更新 UI
                            if current_time - self._last_update_time >= 0.1:
                                elapsed = current_time - self._last_update_time
                                # 本次瞬时速度（单位 B/s）
                                instant_speed = (downloaded - self._last_size) / elapsed
                                
                                # 将瞬时速度加入历史队列
                                self._speed_history.append(instant_speed)
                                if len(self._speed_history) > 3:
                                    self._speed_history.pop(0)
                                
                                # 平滑速度 = 最近几次瞬时速度的平均值
                                avg_speed = sum(self._speed_history) / len(self._speed_history)
                                
                                # 格式化速度字符串
                                speed_str = self.format_speed(avg_speed)
                                
                                # 计算进度百分比（0~100）
                                progress = int((downloaded / total_size) * 100) if total_size > 0 else 0
                                
                                # 异步回到主线程更新 UI：进度条 + 下载信息文本
                                self.root.after(0, lambda p=progress, d=downloaded, t=total_size, s=speed_str: 
                                                self._update_download_info(p, d, t, s))
                                
                                # 更新“上一次”相关数据
                                self._last_update_time = current_time
                                self._last_size = downloaded
            
            # 下载完成后，调用安装程序 (放在主线程)
            self.root.after(0, self._run_installer, download_path)
            
        except Exception as e:
            pass
        finally:
            self.downloading = False

    def _add_download_info_labels(self):
        """添加下载信息标签（单行显示）"""
        if not hasattr(self, 'download_info_frame'):
            # 在 update_window 窗口下创建 一个 Frame
            self.download_info_frame = ttk.Frame(self.update_window)
            self.download_info_frame.pack(pady=(0, 10))
            
            # 创建一个 Label 用来显示“已下载大小 / 总大小 | 速度”
            self.download_info_label = ttk.Label(
                self.download_info_frame,
                text="0.00 MB / 0.00 MB | 速度: 0.00 B/s",
                font=('Microsoft YaHei', 9)
            )
            self.download_info_label.pack()
        
        # 如果你还没有 progress_bar，需要在创建 update_window 的时候把它做出来：
        # 假设在 _create_update_window 中，你已经创建了一个 ttk.Progressbar 并赋值给 self.progress_bar

    def _update_download_info(self, progress, downloaded_bytes, total_bytes, speed_str):
        """
        更新下载信息显示（单行格式）
        :param progress: 进度百分比（0~100）
        :param downloaded_bytes: 已下载字节数
        :param total_bytes: 总字节数
        :param speed_str: 格式化后的速度字符串（例如 "1.23 MB/s"）
        """
        try:
            if self.update_window and self.update_window.winfo_exists():
                # 更新进度条数值
                if self.progress_bar:
                    self.progress_bar['value'] = progress
                
                # 将字节数转换为 MB 格式（保留两位小数）
                downloaded_mb = downloaded_bytes / (1024 * 1024)
                total_mb = total_bytes / (1024 * 1024) if total_bytes > 0 else 0.0
                info_text = f"{downloaded_mb:.2f} MB / {total_mb:.2f} MB | 速度: {speed_str}"
                
                # 更新 Label 文本
                self.download_info_label.config(text=info_text)
                
                # 强制刷新 UI
                self.update_window.update()
        except Exception:
            pass  # 忽略更新 UI 时的任何异常

    def _update_progress(self, progress):
        """更新进度条"""
        try:
            if self.progress_bar and self.update_window and self.update_window.winfo_exists():
                self.progress_bar['value'] = progress
                self.update_window.update()
        except Exception as e:
            pass  # 忽略进度条更新错误

    def _run_installer(self, installer_path):
        """运行安装程序"""
        try:
            # 最小化主窗口
            self.root.iconify()
            
            # 关闭更新窗口
            self._cancel_update()
            
            # 运行安装程序
            subprocess.Popen([installer_path], shell=True)
            
            # 退出当前程序
            self.root.after(1000, self.root.destroy)
            
        except Exception as e:
            self.root.deiconify()
            messagebox.showerror("安装失败", f"无法启动安装程序: {str(e)}")

    def _show_download_error(self, message):
        """显示下载错误"""
        try:
            self._create_update_window(
                f"下载失败: {message}",
                show_progress=False
            )
            if self.update_button:
                self.update_button.config(state="disabled")
            self.root.after(3000, self._cancel_update)
        except Exception as e:
            messagebox.showerror("错误", f"显示下载错误失败: {str(e)}")

    ####以上是检测更新的函数

    def on_treeview_drag_start(self, event):
        """开始拖动时记录选中的行"""
        item = self.tree.identify_row(event.y)
        if item:
            self.dragged_item = item
        else:
            self.dragged_item = None  # 避免残留

    def on_treeview_drag_motion(self, event):
        """拖动过程中高亮鼠标下方的项目"""
        if not hasattr(self, "dragged_item") or self.dragged_item is None:
            return
        
        # 清除之前的高亮
        for item in self.tree.get_children():
            self.tree.item(item, tags=())
        
        # 获取当前鼠标位置下的项目
        target_item = self.tree.identify_row(event.y)
        
        if target_item and target_item != self.dragged_item:
            # 高亮目标项目
            self.tree.tag_configure("drop_target", background="#d9e6ff")
            self.tree.item(target_item, tags=("drop_target",))

    def on_treeview_drag_release(self, event):
        """释放鼠标时将拖动项插入到目标项位置，并更新图片和预览"""
        if not hasattr(self, "dragged_item") or self.dragged_item is None:
            return

        target_item = self.tree.identify_row(event.y)

        # 判断target_item和dragged_item有效且不相同
        if target_item and target_item != self.dragged_item:
            try:
                dragged_index = self.tree.index(self.dragged_item)
                target_index = self.tree.index(target_item)
            except Exception as e:
                self.dragged_item = None
                return

            # 拖动项的值和数据
            dragged_values = self.tree.item(self.dragged_item, "values")
            dragged_image = self.image_list[dragged_index] if dragged_index < len(self.image_list) else None
            dragged_image_data = self.image_dict.get(self.dragged_item)

            # 删除原项
            self.tree.delete(self.dragged_item)
            if dragged_index < len(self.image_list):
                del self.image_list[dragged_index]
            if self.dragged_item in self.image_dict:
                del self.image_dict[self.dragged_item]

            # 插入新项
            new_item = self.tree.insert("", target_index, values=dragged_values)
            if dragged_image is not None:
                self.image_list.insert(target_index, dragged_image)
            if dragged_image_data:
                self.image_dict[new_item] = dragged_image_data

            # 选中新项并更新预览
            self.tree.selection_set(new_item)
            self.dragged_item = new_item  # 更新引用
            self.on_treeview_select(None)
            self.update_image_listbox()

        # 最终清理
        self.dragged_item = None

    def update_label(self, event=None):
        """更新 Label 显示 Treeview 选中的隐藏列数据（带可靠的悬停提示功能）"""

        def 截断文本(文本, 最大像素宽度=None, 控件=None):
            """辅助函数：当文本超出最大像素宽度时添加省略号"""
            文本 = str(文本)
            if 最大像素宽度 is None or 控件 is None:
                return 文本  # 没有提供测量依据则原样返回

            font = tkFont.Font(font=控件['font'])
            if font.measure(文本) <= 最大像素宽度:
                return 文本
            # 截断文本直到合适长度
            for i in range(len(文本), 0, -1):
                截断后 = 文本[:i] + "..."
                if font.measure(截断后) <= 最大像素宽度:
                    return 截断后
            return "..."

        class 悬停提示管理器:
            """管理悬停提示的创建和销毁"""
            def __init__(self, master):
                self.master = master
                self.当前提示 = None

            def 显示提示(self, 控件, 文本):
                self.隐藏提示()
                最大宽度 = int(self.master.winfo_width() * 2 / 5)
                font = tkFont.Font(font=控件['font'])
                if font.measure(文本) > 最大宽度:
                    # 自动换行（按像素分段）
                    每行像素 = 最大宽度
                    当前宽 = 0
                    行 = ""
                    行集 = []
                    for 字符 in 文本:
                        宽 = font.measure(字符)
                        if 当前宽 + 宽 > 每行像素:
                            行集.append(行)
                            行 = 字符
                            当前宽 = 宽
                        else:
                            行 += 字符
                            当前宽 += 宽
                    if 行:
                        行集.append(行)
                    文本 = "\n".join(行集)

                self.当前提示 = tk.Toplevel(self.master)
                self.当前提示.wm_overrideredirect(True)
                x = 控件.winfo_rootx() + 15
                y = 控件.winfo_rooty() + 控件.winfo_height() + 5
                self.当前提示.wm_geometry(f"+{x}+{y}")
                tk.Label(
                    self.当前提示,
                    text=文本,
                    bg="#FFFFE0",
                    relief="solid",
                    borderwidth=1,
                    padx=5,
                    pady=2,
                    justify="left"
                ).pack()

            def 隐藏提示(self):
                if self.当前提示:
                    self.当前提示.destroy()
                    self.当前提示 = None

        # 获取当前选中的项目
        sel = self.tree.selection()
        if not sel:
            self.clear_labels()
            return

        values = self.tree.item(sel[0], "values")
        提示管理器 = 悬停提示管理器(self.root)

        if getattr(self, 'config_filename', None):
            fname = os.path.basename(self.config_filename)
            self.label_filename.config(text=f"({fname})")
        else:
            self.label_filename.config(text="")

        字段配置 = {
            "图片名称": 0,
            "识图区域": 14,
            "条件判断": [6, 7, 9, 11, 12, 13],
            "相似度": 2,
            "点击位置(F2)": 4,
            "键盘动作": 3,
            "鼠标动作": 10,
            "状态": 8
        }

        for 字段名, 索引 in 字段配置.items():
            # 1. 先计算 raw
            if isinstance(索引, (list, tuple)):
                if 字段名 == "条件判断":
                    parts = []
                    # 前半部分条件
                    if len(values) > max(索引[:3]) and any(values[i] for i in 索引[:3]):
                        part1 = []
                        if values[索引[0]]:
                            part1.append(str(values[索引[0]]).strip())
                        part1.append("跳转到")
                        if values[索引[1]]:
                            part1.append(str(values[索引[1]]).strip())
                        if values[索引[2]]:
                            part1.append("需禁用")
                            part1.append(str(values[索引[2]]).strip())
                        parts.append(" ".join(part1))
                    # 后半部分条件
                    if len(values) > max(索引[3:]) and any(values[i] for i in 索引[3:]):
                        part2 = []
                        if values[索引[3]]:
                            part2.append(str(values[索引[3]]).strip())
                        part2.append("跳转到")
                        if values[索引[4]]:
                            part2.append(str(values[索引[4]]).strip())
                        if values[索引[5]]:
                            part2.append("需禁用")
                            part2.append(str(values[索引[5]]).strip())
                        parts.append(" ".join(part2))
                    raw = "；".join(parts) if parts else "默认"
                else:
                    raw_parts = [str(values[i]).replace("\n", " ").strip() for i in 索引]
                    raw_non_empty = [p for p in raw_parts if p]
                    raw = " | ".join(raw_non_empty) if raw_non_empty else "默认"
            else:
                raw = str(values[索引]).replace("\n", " ").strip()

            # 2. 根据字段名渲染
            if 字段名 == "点击位置(F2)":
                is_dynamic = False  # 先默认不是动态

                selected_items = self.tree.selection()
                if selected_items:
                    selected_item = selected_items[0]
                    selected_index = self.tree.index(selected_item)
                    selected_image = self.image_list[selected_index]

                    if selected_image[4]:  # 如果有现有的鼠标操作数据
                        try:
                            parts = selected_image[4].split(":")
                            if len(parts) >= 3:
                                is_dynamic = parts[2] == "1"  # 判断是否为动态坐标
                        except:
                            pass

                if is_dynamic:
                    raw = "自动计算"
                    lbl = self.labels[字段名]
                    lbl.config(text=raw, anchor="e", width=0)

            if 字段名 == "识图区域":
                parts = [p.strip() for p in raw.split("|")]
                coords = parts[0]
                area_choice = parts[1]
                mapped = {"update": "待更新","screenshot": "步骤图片","manual": "自定义"}.get(area_choice, "全屏")
                lbl = self.labels[字段名]
                lbl.unbind("<Enter>")
                lbl.unbind("<Leave>")
                lbl.config(text=mapped, anchor="e", width=0)
                def on_enter(e):
                    font = tkFont.Font(font=e.widget["font"])
                    text_width = font.measure(mapped)
                    label_width = e.widget.winfo_width()
                    text_right_bound = label_width
                    text_left_bound = text_right_bound - text_width
                    if text_left_bound <= e.x <= text_right_bound:
                        提示管理器.显示提示(e.widget, f"{mapped}({coords})")
                lbl.bind("<Enter>", on_enter)
                lbl.bind("<Leave>", lambda e: 提示管理器.隐藏提示())

            elif 字段名 == "条件判断":
                lbl = self.labels[字段名]
                lbl.unbind("<Enter>")
                lbl.unbind("<Leave>")
                # 不截断，直接显示完整raw
                lbl.config(text=raw, anchor="e", width=0)

                if raw == "默认":
                    # raw 为“默认”时，显示固定提示
                    def on_enter_default(e):
                        font = tkFont.Font(font=e.widget["font"])
                        text_width = font.measure(mapped)
                        label_width = e.widget.winfo_width()
                        text_right_bound = label_width
                        text_left_bound = text_right_bound - text_width
                        if text_left_bound <= e.x <= text_right_bound:
                            提示管理器.显示提示(
                                e.widget,
                                "识图成功跳转到下一个步骤，识图失败重试当前步骤"
                            )
                    lbl.bind("<Enter>", on_enter_default)
                    lbl.bind("<Leave>", lambda e: 提示管理器.隐藏提示())
                else:
                    # raw 非“默认”时，走原有的截断+提示逻辑
                    max_width = int(self.root.winfo_width() * 3 / 10)
                    disp = 截断文本(raw, max_width, lbl)
                    lbl.config(text=disp)
                    font = tkFont.Font(font=lbl['font'])
                    if font.measure(raw) > max_width:
                        lbl.bind(
                            "<Enter>",
                            lambda e, t=raw: 提示管理器.显示提示(e.widget, t)
                        )
                        lbl.bind("<Leave>", lambda e: 提示管理器.隐藏提示())

            else:
                # 其它字段，沿用原有逻辑
                lbl = self.labels[字段名]
                lbl.unbind("<Enter>")
                lbl.unbind("<Leave>")
                max_width = int(self.root.winfo_width() * 3 / 10)
                disp = 截断文本(raw, max_width, lbl)
                lbl.config(text=disp)
                font = tkFont.Font(font=lbl['font'])
                if font.measure(raw) > max_width:
                    lbl.bind(
                        "<Enter>",
                        lambda e, t=raw: 提示管理器.显示提示(e.widget, t)
                    )
                    lbl.bind("<Leave>", lambda e: 提示管理器.隐藏提示())


    def clear_labels(self):
        """清空 Label 内容"""
        # 清空各字段
        for lbl in self.labels.values():
            lbl.config(text="")
        # 清空配置文件名（同一行）
        self.label_filename.config(text="")

    def register_global_hotkey(self):
        try:
            # 注册开始/停止热键
            def main_hotkey_callback():
                self.root.after(0, self.toggle_script)
                
            main_hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
            keyboard.add_hotkey(main_hotkey_str, main_hotkey_callback)
            
            # 注册截图热键
            def screenshot_hotkey_callback():
                self.root.after(0, self.prepare_capture_screenshot)
                
            keyboard.add_hotkey(self.screenshot_hotkey, screenshot_hotkey_callback)

            # 注册重新截图热键
            def retake_image_hotkey_callback():
                self.root.after(0, self.retake_screenshot)
                
            keyboard.add_hotkey(self.retake_image_hotkey, retake_image_hotkey_callback)

            # 注册更改点击坐标热键
            def change_coodr_hotkey_callback():
                self.root.after(0, self.get_mouse_position)
                
            keyboard.add_hotkey(self.change_coodr_hotkey, change_coodr_hotkey_callback)
            
            # 日志记录
            print("-" * 85)
            logging.info("-" * 85)
            logging.info("程序启动 - 热键注册完成\n开始/停止  F9\n截图  F8\n重新截图  F4\n更改点击坐标  F2")
            
        except Exception as e:
            print(f"注册热键失败: {e}")
            logging.error(f"热键注册失败: {e}")

    def unregister_global_hotkey(self):
        try:
            # 注销热键
            main_hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
            keyboard.remove_hotkey(main_hotkey_str)
            keyboard.remove_hotkey(self.screenshot_hotkey)
            keyboard.remove_hotkey(self.retake_image_hotkey)
            keyboard.remove_hotkey(self.change_coodr_hotkey)
            
        except Exception as e:
            print(f"注销全局热键出错：{e}")
            logging.error(f"热键注销失败: {e}")
 
    def prepare_capture_screenshot(self, event=None):
        # 如果 self.top 已存在且窗口未关闭，则直接返回或销毁旧窗口
        if hasattr(self, 'top') and self.top:
            try:
                # 检查窗口是否仍然有效
                if self.top.winfo_exists():
                    # 方案1：直接返回，不创建新窗口
                    # return
                    
                    # 方案2：销毁旧窗口，创建新窗口
                    self.top.destroy()
            except tk.TclError:
                # 如果窗口已被手动关闭，清除引用
                self.top = None

        # 捕获全屏快照
        screenshot = ImageGrab.grab()
        self.full_screen_image = screenshot
        self.screenshot_photo = ImageTk.PhotoImage(screenshot)

        # 计算新的步骤编号
        existing_steps = set()
        for item in self.image_list:
            step_name = item[1]
            if step_name.startswith("步骤"):
                try:
                    num = int(step_name[2:])
                    existing_steps.add(num)
                except ValueError:
                    continue
        new_step_num = 1
        while new_step_num in existing_steps:
            new_step_num += 1
        self._next_step_num = new_step_num

        # 创建全屏窗口
        self.top = tk.Toplevel(self.root)
        self.top.attributes('-fullscreen', True)
        self.top.attributes('-topmost', True)
        self.top.focus_force()
        self.top.bind("<Escape>", self.exit_screenshot_mode)

        # 初始化 Canvas
        self.canvas = tk.Canvas(self.top, cursor="crosshair")
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.image_id = self.canvas.create_image(0, 0, anchor=tk.NW, image=self.screenshot_photo)

        # 绑定鼠标事件...
        self.rect = None
        self.overlay_rects = []
        self.canvas.bind("<ButtonPress-1>", self.on_button_press)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_button_release)

        # 窗口关闭时清理引用
        self.top.protocol("WM_DELETE_WINDOW", self.cleanup_screenshot_window)

        # 在窗口呈现后，延迟执行一次自动点击
        self.top.after(100, self._auto_click_current_position)  # 设置延迟 100 毫秒
        self.top.after(1000, self._auto_click_current_position)

    def _auto_click_current_position(self):
        if not self.is_dragging:
            try:
                # 获取当前鼠标位置（全局屏幕坐标）
                x, y = pyautogui.position()
                # 执行左键点击
                pyautogui.click(x, y)
            except Exception as e:
                print(f"自动点击失败: {e}")

    def cleanup_screenshot_window(self):
        """清理截图窗口引用"""
        if hasattr(self, 'top') and self.top:
            self.top.destroy()
        self.top = None
                
    def exit_screenshot_mode(self, event=None):
        """退出截图模式，关闭透明窗口，恢复主窗口"""
        if hasattr(self, 'top') and self.top:  # 确保 self.top 存在
            self.top.destroy()
            self.top = None  # 释放引用，防止重复调用时报错
   
    def on_button_press(self, event):
        # 记录起始点
        self.start_x = event.x
        self.start_y = event.y

        # 如果之前已有选框，删除
        if hasattr(self, 'rect') and self.rect:
            self.canvas.delete(self.rect)
            self.rect = None

        # 仅创建选框，不再创建遮罩
        self.rect = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y,
            outline='#0773fc', width=2
        )
        # 确保选框在最上层
        self.canvas.tag_raise(self.rect)

    def on_mouse_drag(self, event):
        self.is_dragging = True
        cur_x, cur_y = event.x, event.y
        # 更新选框坐标
        if hasattr(self, 'rect') and self.rect:
            self.canvas.coords(self.rect, self.start_x, self.start_y, cur_x, cur_y)
        # 去掉 update_overlay 调用，不再更新遮罩

    def on_button_release(self, event):
        self.is_dragging = False
        end_x, end_y = event.x, event.y
        dx = abs(end_x - self.start_x)
        dy = abs(end_y - self.start_y)
        threshold = 5
        # 如果跳过或太小，删除选框和覆盖层
        if getattr(self, 'skip_next_draw', False) or (dx < threshold and dy < threshold):
            self.skip_next_draw = False
            if hasattr(self, 'rect') and self.rect:
                self.canvas.delete(self.rect)
                self.rect = None
            # 删除覆盖层
            if hasattr(self, 'overlay_rects'):
                for item in self.overlay_rects:
                    self.canvas.delete(item)
                self.overlay_rects = []
            return
        # 最终保留选区后，若不再需要覆盖层，也可以在这里删除
        # 例如：释放后移除覆盖层，只留下选框
        if hasattr(self, 'overlay_rects'):
            for item in self.overlay_rects:
                self.canvas.delete(item)
            self.overlay_rects = []

        # 获取截图区域，不包括矩形框
        border_offset = 2  # 让截图区域比矩形框内缩 2 像素
        
        # 确保 left <= right 和 top <= bottom
        left = min(self.start_x, end_x) + border_offset
        right = max(self.start_x, end_x) - border_offset
        top = min(self.start_y, end_y) + border_offset
        bottom = max(self.start_y, end_y) - border_offset

        # 检查是否有效区域（防止宽度或高度为负数）
        if right <= left or bottom <= top:
            print("无效截图区域：宽度或高度为 0")
            return

        # 转换为整数（PIL 需要整数坐标）
        bbox = (int(left), int(top), int(right), int(bottom))

        # 构造截图区域字符串,“screenshot”为选项默认值
        img_left, img_top, img_right, img_bottom = left, top, right, bottom
        recognition_area = f"{left},{top},{right},{bottom}|screenshot|{img_left},{img_top},{img_right},{img_bottom}"  
    
        # 使用规则 "截图（时间）.png" 命名截图文件避免重复
        timestamp = datetime.now().strftime("%Y%m%d%H%M%S")  # 生成时间戳
        screenshot_path = os.path.join(self.screenshot_folder, f"{timestamp}.png")

        # 确保截图文件夹存在
        os.makedirs(self.screenshot_folder, exist_ok=True)

        # 截图指定区域
        screenshot = ImageGrab.grab(bbox)
        screenshot.save(screenshot_path)

        # 计算截图区域的中心坐标
        center_x = (min(self.start_x, end_x) + max(self.start_x, end_x)) // 2
        center_y = (min(self.start_y, end_y) + max(self.start_y, end_y)) // 2
        mouse_click_coordinates = f"{center_x},{center_y}"  # 使用中心坐标

        # 更新图像列表
        if self.need_retake_screenshot:
            selected = self.tree.selection()
            if selected:
                selected_item = selected[0]
                selected_index = self.tree.index(selected_item)
                selected_image = self.image_list[selected_index]  # 获取原始数据
                insert_index = selected_index
                
                # 1. 先删除旧的图片文件（如果存在）
                old_image_path = selected_image[0]  # 原图片路径
                try:
                    if os.path.exists(old_image_path):
                        # 获取原图片所在目录
                        old_dir = os.path.dirname(old_image_path)                 
                        # 获取截图文件名
                        screenshot_filename = os.path.basename(screenshot_path)                   
                        # 构造新路径（移动到原图片所在目录）
                        new_screenshot_path = os.path.join(old_dir, screenshot_filename)
                        
                        # 只有当新旧路径不同时才执行移动操作
                        if new_screenshot_path != screenshot_path:             
                            # 移动文件
                            if os.path.exists(screenshot_path):
                                # 如果目标位置已有文件，先删除
                                if os.path.exists(new_screenshot_path):
                                    os.remove(new_screenshot_path)
                                os.rename(screenshot_path, new_screenshot_path)                      
                            # 更新 screenshot_path 为新路径
                            screenshot_path = new_screenshot_path
                        
                        # 删除旧图片
                        os.remove(old_image_path)
                        
                except Exception as e:
                    print(f"操作失败: {e}")
                
                # 2. 处理鼠标动作数据
                if selected_image[4] and ":" in selected_image[4]:  # 如果有现有的鼠标动作数据
                    parts = selected_image[4].split(":")
                    action = parts[0]
                    dynamic = parts[2] if len(parts) > 2 else "0"
                    count = parts[3] if len(parts) > 3 else "1"
                    # 重新构建鼠标动作字符串
                    mouse_action = f"{action}:{center_x},{center_y}:{dynamic}"
                    if action in ["click", "scrollUp", "scrollDown"]:
                        mouse_action += f":{count}"
                else:
                    # 如果没有鼠标动作数据，使用默认的单击动作
                    mouse_action = f"click:{center_x},{center_y}:0:1"

                #处理识图区域
                original_area_str = selected_image[14] 
                # 直接按 "|" 分割成三部分
                coords, area_choice_value, img_coords = original_area_str.split("|")
                # 解析步骤图片坐标
                l, t, r, b = map(int, img_coords.split(","))   
                l, t, r, b = img_left, img_top, img_right, img_bottom 
                 # 重新构建识图区域字符串
                if area_choice_value == 'screenshot':
                    new_area_str = f"{l}, {t}, {r}, {b}|{area_choice_value}|{l}, {t}, {r}, {b}"
                else:
                    new_area_str = f"{coords}|{area_choice_value}|{l}, {t}, {r}, {b}"
                print(new_area_str)

                # 创建更新后的数据元组
                updated_image = (
                    screenshot_path,          # 0: 新的图片路径
                    selected_image[1],       # 1: 步骤名称
                    selected_image[2],       # 2: 相似度阈值
                    selected_image[3],       # 3: 键盘动作
                    mouse_action,            # 4: 更新后的鼠标动作
                    selected_image[5],       # 5: 等待时间
                    selected_image[6],       # 6: 条件
                    selected_image[7],       # 7: 需跳转
                    selected_image[8],       # 8: 状态
                    selected_image[9],      # 9: 【需禁用】目标
                    selected_image[10],     # 10: 鼠标动作
                    selected_image[11],       # 11: 条件2
                    selected_image[12],      # 12: 需跳转2
                    selected_image[13],      # 13: 需禁用2
                    new_area_str,      # 13: 识图区域
                    #新增索引
                )

                # 4. 更新数据源
                self.image_list[selected_index] = updated_image
                self.need_retake_screenshot = False  
                
        else:
            if self.config_filename and os.path.exists(self.config_filename):
                old_image_path = screenshot_path  # 原图片路径
                config_basename = Path(self.config_filename).stem  # 获取不带扩展名的配置文件名
                config_folder_dir = Path(self.screenshot_folder) / config_basename  # 构造目标目录

                try:
                    # 确保目标目录存在（使用相对路径）
                    config_folder_dir.mkdir(parents=True, exist_ok=True)
                    
                    # 将路径转换为Path对象便于处理
                    old_path = Path(old_image_path)
                    new_path = config_folder_dir / old_path.name
                    
                    if old_path.exists():
                        # 只有当新旧路径不同时才执行移动操作
                        if str(new_path) != str(old_path):
                            # 如果目标位置已有文件，先删除
                            if new_path.exists():
                                new_path.unlink()
                            
                            # 移动文件（使用rename保持相对路径）
                            old_path.rename(new_path)
                            
                            # 更新screenshot_path为新路径（保持相对路径）
                            screenshot_path = str(new_path)
                        else:
                            print("源路径和目标路径相同，跳过移动操作")
                    else:
                        print(f"原图片不存在: {old_image_path}")

                except Exception as e:
                    print(f"操作失败: {e}")
                    print(f"原路径: {old_path}")
                    print(f"新路径: {new_path}")
                    print(f"当前工作目录: {os.getcwd()}")
                    
            selected_item = self.tree.selection()  # 获取当前选中的项
            step_name = f"步骤{self._next_step_num}"  # 生成递增的步骤名称
            if selected_item:   
                selected_index = self.tree.index(selected_item[0])  # 获取选中项的索引
                insert_index = selected_index + 1  # 在选中项的下一行插入新项目
                self.image_list.insert(insert_index, (screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次", "", "", "", recognition_area))#新增索引
            else:
                self.image_list.append((screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次", "", "", "", recognition_area))#新增索引

        self.update_image_listbox()  # 更新详细信息
        self.top.destroy()       # 关闭全屏透明窗口
        self.root.deiconify()  # 重新显示窗口

        # 确保 tree 更新完成后再选择最新项目
        all_items = self.tree.get_children()
        if all_items:
            if selected_item:
                # 如果是在选中项的下一行插入，则聚焦到新插入的项目
                last_item = all_items[insert_index]  # 获取新插入的项目
            else:
                # 如果没有选中项，则聚焦到最后一个项目
                last_item = all_items[-1]
            self.tree.selection_set(last_item)  # 选择该项目
            self.tree.focus(last_item)  # 聚焦到该项目
            self.tree.see(last_item)  # 滚动到可见区域
            print(f"聚焦到项目: {last_item}")
        else:
            print("没有可用的项目")
        self.update_label() # 更新详细信息
        
        if self.thread is not None:
            # 设置停止标志（如果线程支持）
            self.running = False
            
            # 尝试正常停止
            self.thread.join(timeout=1)  # 等待1秒
            
            if self.thread.is_alive():
                print("警告：脚本线程未能在1秒内停止，尝试强制终止")
                logging.warning("脚本线程未能在1秒内停止，尝试强制终止")
                
                # 强制终止线程（不推荐，但可用）
                try:
                    import ctypes
                    thread_id = self.thread.ident
                    res = ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id, ctypes.py_object(SystemExit))
                    if res == 0:
                        raise ValueError("无效的线程ID")
                    elif res != 1:
                        ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id, 0)
                        raise SystemError("PyThreadState_SetAsyncExc失败")
                except Exception as e:
                    print(f"强制终止线程失败: {e}")
                    logging.error(f"强制终止线程失败: {e}")
        
                self.thread = None
                print("脚本已停止")
                logging.info("脚本已停止")
                self.root.after(0, self.update_ui_after_stop)

    def retake_screenshot(self, event=None):
        selected_item = self.tree.selection()
        if selected_item:
            self.need_retake_screenshot = True     
            self.prepare_capture_screenshot()
        else:
            messagebox.showerror("错误", "请选中1个步骤后重试")
            return
   
    def update_image_listbox(self,filter_text=""):
        try:   
            # 保存当前预览状态
            current_preview = None
            if hasattr(self.preview_image_label, 'image'):
                current_preview = self.preview_image_label.image
            
            # 保存当前选中项的索引和焦点索引
            selected_indices = [self.tree.index(item) for item in self.tree.selection()]
            focused_index = self.tree.index(self.tree.focus()) if self.tree.focus() else None
            
            # 清空旧的列表项
            for row in self.tree.get_children():
                self.tree.delete(row)

            # 插入新项，显示图片名称和延时ms
            for index, item in enumerate(self.image_list):
                try:
                    if not item or len(item) < 1:  # 检查项目是否有效
                        continue

                    img_path = item[0]
                    if not os.path.exists(img_path):
                        print(f"警告：图像文件不存在 {img_path}")
                        logging.warning(f"图像文件不存在 {img_path}")
                        continue
                    full_item = list(item)
                    # 确保数据完整，若字段不足则补空字符串
                    while len(full_item) < 15: #新增索引
                        full_item.append("")

                    # 解包所有列（包括新增的“状态”列和“需禁用”列）
                    (
                        img_path, 
                        step_name, 
                        similarity_threshold, 
                        keyboard_input, 
                        mouse_click_coordinates, 
                        wait_time, 
                        condition, 
                        jump_to, 
                        status,
                        steps_to_disable,
                        mouse_action_result,
                        condition_2,
                        jump_to_2,
                        steps_to_disable_2,
                        recognition_area,
                        #新增索引
                    ) = full_item

                    # ✅ 添加搜索关键词过滤条件
                    if filter_text:
                        if not step_name or filter_text.lower() not in step_name.lower():
                            continue

                    # 提取坐标部分
                    coords = mouse_click_coordinates.split(":")[1] if mouse_click_coordinates and ":" in mouse_click_coordinates else mouse_click_coordinates

                    # 加载图像并创建缩略图
                    try:
                        image = Image.open(img_path)
                        image.thumbnail((50, 50))
                        photo = ImageTk.PhotoImage(image)

                        # 插入所有数据（包括“状态”列）
                        tree_item = self.tree.insert("", tk.END, values=(
                            os.path.basename(img_path), 
                            step_name, 
                            similarity_threshold, 
                            keyboard_input, 
                            coords,  # 只显示x,y
                            wait_time,
                            condition,
                            jump_to,
                            status, 
                            steps_to_disable,
                            mouse_action_result,
                            condition_2,
                            jump_to_2,
                            steps_to_disable_2,
                            recognition_area,
                            #新增索引
                        ), image=photo)
                        self.tree.image_refs.append(photo)  # 保持对图像的引用

                        # 插入新项后检查status是否为【禁用】
                        if status == "禁用":
                            self.tree.item(tree_item, tags=("disabled",))
                    except Exception as e:
                        logging.error(f"处理图像 {img_path} 时出错: {e}")
                except Exception as ex:
                    logging.error(f"处理列表项时出错: {ex}")

            # 恢复选择状态（基于索引）
            children = self.tree.get_children()
            new_selection = []
            for idx in selected_indices:
                if idx < len(children):  # 防止索引越界
                    new_selection.append(children[idx])
            if new_selection:
                self.tree.selection_set(new_selection)

            # 恢复焦点状态（基于索引）
            if focused_index is not None and focused_index < len(children):
                self.tree.focus(children[focused_index])
                self.tree.see(children[focused_index])  # 滚动到焦点项

            # 恢复预览状态
            if current_preview:
                self.preview_image_label.config(image=current_preview)
                self.preview_image_label.image = current_preview    
            
        except Exception as e:
            print(f"更新列表时出错: {e}")
            logging.error(f"更新列表时出错: {e}")
        # 在更新列表后如果没有选中项，显示默认图像
        if not self.tree.selection():
            self.load_default_image()
            self.clear_labels()

        # 只有在配置文件名非空且文件存在时才执行更新
        if self.config_filename and os.path.exists(self.config_filename) and not self.step_on_search:
            with open(self.config_filename, 'r', encoding='utf-8') as f:
                config = json.load(f)    
            self.loop_count = int(self.loop_count_entry.get())
            config = {
                'hotkey': self.hotkey,
                'similarity_threshold': self.similarity_threshold,
                'delay_time': self.delay_time,
                'loop_count': self.loop_count,
                'image_list': [img for img in self.image_list if os.path.exists(img[0])],
                'only_keyboard': self.only_keyboard_var.get(),
            }

            # 保存到配置文件
            with open(self.config_filename, 'w', encoding='utf-8') as f:
                json.dump(config, f, ensure_ascii=False, indent=4)
            
            if self.config_loaded:
                self.config_loaded = False
            else:
                print("已更新配置文件:", self.config_filename)
                logging.info("已更新配置文件: %s", self.config_filename)

        self.step_on_search = False
   
    def delete_selected_image(self):
        try:
            selected_items = self.tree.selection()
            if not selected_items:
                messagebox.showinfo("提示", "请先选择要删除的项目")
                return

            count = len(selected_items)
            if not messagebox.askyesno("确认删除", f"是否删除这 {count} 个步骤及对应的图片文件？"):
                return

            # 计算索引并倒序删除
            indices = [self.tree.index(item) for item in selected_items]
            indices.sort(reverse=True)

            paths_to_check = []
            for idx in indices:
                if 0 <= idx < len(self.image_list):
                    paths_to_check.append(self.image_list[idx][0])
                    del self.image_list[idx]
                else:
                    logging.warning(f"选中的索引超出范围: {idx}")

            # 删除硬盘文件
            for img_path in set(paths_to_check):
                if not any(item[0] == img_path for item in self.image_list) and os.path.exists(img_path):
                    try:
                        os.remove(img_path)
                        logging.info(f"图像文件已删除: {img_path}")
                    except Exception as e:
                        logging.error(f"删除图像文件时出错: {e}")

            # 刷新界面
            self.update_image_listbox()
            self.load_default_image()
            self.clear_labels()

            #清空复制缓存
            self.copied_items.clear()
            self.cut_original_indices.clear()

            # —— 强制清除所有选中和焦点 —— 
            self.tree.selection_remove(self.tree.selection())

        except Exception as e:
            logging.error(f"删除图像时出错: {e}")


    def toggle_script(self, event=None):
        if self.toggle_run_button.cget("text") == "停止运行(F9)":
            self.stop_script()
            return
        
        if not self.running:
            if not self.image_list:
                messagebox.showwarning("提示", "列表中无步骤，【截取图片】【加载配置】【导入配置】可添加步骤")
                return  # 直接返回，不执行后续代码
            if self.from_step:
                selected_items = self.tree.selection()
                selected_item = selected_items[0]
                self.start_step_index = self.tree.index(selected_item)
                self.from_step = False
            else:
                self.start_step_index = 0  
            self.toggle_run_button.config(text="停止运行(F9)")
            if self.allow_minimize_var.get():  # 检查勾选框状态
                self.root.iconify()  # 最小化主窗口
            else:
                self.root.lift()  # 确保主窗口在最上层
            self.start_script_thread()

    def start_script_thread(self):
        if not self.running:
            self.running = True
            self.thread = threading.Thread(target=self.run_script, daemon=True)
            self.thread.start()
   
    def run_script(self):
        try:
            self.loop_count = int(self.loop_count_entry.get())
            if self.loop_count < 0:
                raise ValueError("循环次数不能为负数")
        except ValueError as e:
            messagebox.showerror("输入错误", f"请输入有效的非负整数作为循环次数: {str(e)}")
            self.running = False
            self.root.after(0, self.update_ui_after_stop)
            return

        # 获取所有子项
        children = self.tree.get_children()
        # 检查索引是否有效
        if self.start_step_index < len(children):
            tree_item = children[self.start_step_index]  # 获取对应的 item ID
            item_values = self.tree.item(tree_item, 'values')  # 获取该行的值列表
            self.current_step_name = item_values[1] if item_values and len(item_values) > 1 else "未知步骤"
        else:
            self.current_step_name = "无效步骤索引"
        if self.loop_count == 0:
            print(f"从【{self.current_step_name}】开始执行，无限循环")
            logging.info(f"从【{self.current_step_name}】开始执行，无限循环")            
        else:
            print(f"从【{self.current_step_name}】开始执行，循环{self.loop_count}次")
            logging.info(f"从【{self.current_step_name}】开始执行，循环{self.loop_count}次")

        # 初始化步骤索引映射，假定步骤名称唯一
        self.step_index_map = {step[1]: idx for idx, step in enumerate(self.image_list)}

        self.current_loop = 0

        while self.running and (self.current_loop < self.loop_count or self.loop_count == 0):
            if self.paused:
                time.sleep(0.1)
                continue
            print(f">>开始执行第{self.current_loop + 1}次循环<<")
            logging.info(f">>开始执行第{self.current_loop + 1}次循环<<")
            index = self.start_step_index
            while index < len(self.image_list) and self.running:
                # 获取当前 TreeView 项
                tree_item = self.tree.get_children()[index]
                item_values = list(self.tree.item(tree_item, 'values'))
                self.current_step_name = item_values[1]
                print(f"开始执行【{self.current_step_name}】")
                logging.info(f"开始执行【{self.current_step_name}】")
                # 判断当前项是否被禁用（状态存放在索引 8）
                if self.item_is_disabled(tree_item):
                    print(f"【{self.current_step_name}】被禁用，跳过执行")
                    logging.info(f"【{self.current_step_name}】被禁用，跳过执行")
                    index += 1
                    continue

                self.root.after(0, lambda idx=index: self.focus_on_step(idx))

                current_step = self.image_list[index]
                img_path = current_step[0]
                img_name = current_step[1]
                similarity_threshold = current_step[2]
                keyboard_input = current_step[3]
                mouse_click_coordinates = current_step[4]
                wait_time = current_step[5]
                condition = current_step[6] if len(current_step) > 6 else ""
                jump_to = current_step[7] if len(current_step) > 7 else ""
                disable_target = current_step[9] if len(current_step) > 9 else ""
                condition_2 = current_step[11] if len(current_step) > 11 else ""
                jump_to_2 = current_step[12] if len(current_step) > 12 else ""
                disable_target_2 = current_step[13] if len(current_step) > 13 else ""

                # 执行图像匹配或键盘操作
                if mouse_click_coordinates and not self.only_keyboard_var.get():
                    match_result = self.match_and_click(img_path, similarity_threshold)
                elif os.path.exists(img_path):
                    match_result = self.match_and_click(img_path, similarity_threshold)
                else:
                    match_result = True if keyboard_input else False
                

                # 等待（将毫秒转换为秒）
                if wait_time > 0:
                    time.sleep(wait_time / 1000.0)

                if condition == "识图成功" and match_result:

                    if jump_to in self.step_index_map:
                        index = self.step_index_map[jump_to] -1
                        print(f"从【{img_name}】跳转到【{jump_to}】")
                        logging.info(f"从【{img_name}】跳转到【{jump_to}】")

                    if disable_target in self.step_index_map:
                        target_index = self.step_index_map[disable_target]
                        target_image = list(self.image_list[target_index])
                        # 仅在目标项未被禁用时更新
                        if target_image[8] != "禁用":
                            target_image[8] = "禁用"
                            self.image_list[target_index] = tuple(target_image)
                            # 同步更新 TreeView 显示
                            target_item = self.tree.get_children()[target_index]
                            values = list(self.tree.item(target_item, 'values'))
                            values[8] = "禁用"
                            self.tree.item(target_item, values=tuple(values))
                            print(f"{disable_target} 已被禁用")
                else:
                    # 重新匹配
                    if not match_result and not condition_2:
                        match_result = self.retry_until_match(img_path, similarity_threshold, wait_time)

                if condition_2 == "识图失败" and not match_result:

                    if jump_to_2 in self.step_index_map:
                        index = self.step_index_map[jump_to_2] -1
                        print(f"从【{img_name}】跳转到【{jump_to_2}】")
                        logging.info(f"从【{img_name}】跳转到【{jump_to_2}】")

                    if disable_target_2 in self.step_index_map:
                        target_index = self.step_index_map[disable_target_2]
                        target_image = list(self.image_list[target_index])
                        # 仅在目标项未被禁用时更新
                        if target_image[8] != "禁用":
                            target_image[8] = "禁用"
                            self.image_list[target_index] = tuple(target_image)
                            # 同步更新 TreeView 显示
                            target_item = self.tree.get_children()[target_index]
                            values = list(self.tree.item(target_item, 'values'))
                            values[8] = "禁用"
                            self.tree.item(target_item, values=tuple(values))
                            print(f"{disable_target_2} 已被禁用")

                index += 1
                self.retry_count = 0
                print(f"【{self.current_step_name}】执行完毕")
                logging.info(f"【{self.current_step_name}】执行完毕")

            self.current_loop += 1
            self.start_step_index = 0 
            remain_times = self.loop_count - self.current_loop
            if remain_times > 0:
                self.loop_count_entry.delete(0, "end")  # 清空当前内容
                self.loop_count_entry.insert(0, str(remain_times)) 

        self.restore_disabled_steps()
        self.running = False
        self.root.after(0, self.update_ui_after_stop)
        self.loop_count_entry.delete(0, "end")  # 清空当前内容
        self.loop_count_entry.insert(0, "1")    # 强制插入 1
        self.loop_count = int(self.loop_count_entry.get())
        print(f"所有步骤已执行完毕，已循环{self.current_loop}次")
        logging.info(f"所有步骤已执行完毕，已循环{self.current_loop}次") 
        print(f"-------------------------------------------------------------------------------------")
        logging.info(f"-------------------------------------------------------------------------------------")    

    def restore_disabled_steps(self):
        """
        遍历 image_list，恢复所有因其他步骤设置【需禁用】而被禁用的目标步骤状态为“启用”，
        并同步更新 TreeView 显示。
        """
        # 收集所有被引用为 disable_target 的步骤名称（索引 9 和 13）
        disable_targets = set()
        for step in self.image_list:
            if len(step) > 9 and step[9]:
                disable_targets.add(step[9])
            if len(step) > 13 and step[13]:
                disable_targets.add(step[13])

        # 遍历 image_list，检查那些步骤的名称是否在 disable_targets 内，且当前状态为 "禁用"
        for idx, step in enumerate(self.image_list):
            step_name = step[1]
            if step_name in disable_targets and step[8] == "禁用":
                updated_step = step[:8] + ("启用", step[9])
                self.image_list[idx] = updated_step
                tree_item = self.tree.get_children()[idx]
                values = list(self.tree.item(tree_item, "values"))
                values[8] = "启用"
                self.tree.item(tree_item, values=tuple(values))
                self.tree.item(tree_item, tags=())
                print(f"已恢复 {step_name} 的状态为启用")

    def retry_until_match(self, img_path, similarity_threshold, wait_time):
        """
        重试匹配直到成功或脚本停止
        """
        match_result = False
        while not match_result and self.running:
            time.sleep(wait_time / 1000.0)
            if os.path.exists(img_path):
                match_result = self.match_and_click(img_path, similarity_threshold)
                self.retry_count += 1
                print(f"重试次数{self.retry_count}")
                logging.info(f"重试次数{self.retry_count}")
        return match_result
   
    def stop_script(self):
        if self.thread is not None:
            # 设置停止标志（如果线程支持）
            self.running = False
            self.retry_count = 0
            
            if self.thread.is_alive():
                # 强制终止线程（不推荐，但可用）
                try:
                    import ctypes
                    thread_id = self.thread.ident
                    res = ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id, ctypes.py_object(SystemExit))
                    if res == 0:
                        raise ValueError("无效的线程ID")
                    elif res != 1:
                        ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id, 0)
                        raise SystemError("PyThreadState_SetAsyncExc失败")
                except Exception as e:
                    print(f"强制终止线程失败: {e}")
                    logging.error(f"强制终止线程失败: {e}")
        
        self.thread = None
        self.root.after(0, self.update_ui_after_stop)
        self.restore_disabled_steps()

        result = self.loop_count - self.current_loop  # 计算结果
        display_value = max(0, result)  # 如果结果为负数，则设为 0
        self.loop_count_entry.delete(0, "end")  # 清空当前内容
        self.loop_count_entry.insert(0, str(display_value))  # 插入新值（确保非负）
        self.loop_count = int(self.loop_count_entry.get())
        
        print(f"脚本已停止在第{self.current_loop}次循环的【{self.current_step_name}】")
        logging.info(f"脚本已停止在第{self.current_loop}次循环的【{self.current_step_name}】")
        print(f"-------------------------------------------------------------------------------------")
        logging.info(f"-------------------------------------------------------------------------------------")  
   
    def update_ui_after_stop(self):
        self.toggle_run_button.config(text="开始运行(F9)")   
        self.root.deiconify()  # 恢复主窗口
   
    def move_item_up(self, event=None):
        selected_item = self.tree.selection()   
        if selected_item:
            selected_index = self.tree.index(selected_item[0])
            if selected_index > 0:
                   
                self.image_list[selected_index], self.image_list[selected_index - 1] = self.image_list[selected_index - 1], self.image_list[selected_index]
                self.update_image_listbox()
   
                   
                item_id = self.tree.get_children()[selected_index - 1]
                self.tree.selection_set(item_id)
                self.tree.focus(item_id)
   
    def move_item_down(self, event=None):
        selected_item = self.tree.selection()
        if selected_item:
            selected_index = self.tree.index(selected_item[0])
            if selected_index < len(self.image_list) - 1:
                   
                self.image_list[selected_index], self.image_list[selected_index + 1] = self.image_list[selected_index + 1], self.image_list[selected_index]
                self.update_image_listbox()          
                item_id = self.tree.get_children()[selected_index + 1]
                self.tree.selection_set(item_id)
                self.tree.focus(item_id)
   
    def match_and_click(self, template_path, similarity_threshold):
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        fullscreen_coodrs = f"0,0,{screen_w},{screen_h}"
        # 图像识别匹配
        # 获取当前步骤的完整信息
        selected_index = next((i for i, item in enumerate(self.image_list) if item[0] == template_path), None)
        if selected_index is not None:
            current_step = self.image_list[selected_index]
            mouse_coordinates = current_step[4]  # 获取鼠标坐标
            keyboard_input = current_step[3]  # 获取键盘输入
            step_name = current_step[1] #获取步骤名称
            similarity_threshold = current_step[2] #获取相似度
            # 从selected_items[14]获取识别范围，并取"|"分隔的第一段
            recognition_area = current_step[14].split("|")[0] if len(current_step) > 14 else fullscreen_coodrs
            area_choice_value = current_step[14].split("|")[1] if len(current_step) > 14 else 'fullscreen'
            img_area = current_step[14].split("|")[2] if len(current_step) > 14 else fullscreen_coodrs
        # 检查模板图像是否存在
        if not os.path.exists(template_path):
            raise FileNotFoundError(f"【{step_name}】，找不到模板图像：{template_path}")

        # 读取模板图像（使用 cv2.imdecode 方式解决中文路径问题）
        with open(template_path, 'rb') as f:
            file_bytes = np.asarray(bytearray(f.read()), dtype=np.uint8)
        template = cv2.imdecode(file_bytes, cv2.IMREAD_COLOR)
        if template is None:
            raise ValueError(f"【{step_name}】，无法加载模板图像：{template_path}")

        # 如果有识别范围，则截取指定区域的屏幕图像进行匹配
        if recognition_area:
            # 获取屏幕截图
            screenshot = pyautogui.screenshot()
            screenshot = cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)
            x1 = y1 = 0  # 动态点击初始偏移量
            
            if area_choice_value not in ('fullscreen', 'update'):
                try:
                    x1, y1, x2, y2 = map(int, recognition_area.split(","))
                    # 确保坐标在合理范围内
                    x1 = max(0, x1)
                    y1 = max(0, y1)
                    x2 = min(screenshot.shape[1], x2)
                    y2 = min(screenshot.shape[0], y2)
                    # 截取指定区域
                    screenshot = screenshot[y1:y2, x1:x2]
                except Exception as e:
                    print(f"【{step_name}】，识别范围格式错误：{recognition_area}，错误：{str(e)}")
                    # 如果识别范围格式错误，则使用全屏匹配

            # 执行模板匹配
            result = cv2.matchTemplate(screenshot, template, cv2.TM_CCOEFF_NORMED)
            min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(result)

        # 确保 max_val 是非负数
        if max_val < 0:
            max_val = 0

        if max_val >= similarity_threshold:

            if area_choice_value == 'update':
                locations = np.where(result >= similarity_threshold)
                match_points = list(zip(*locations[::-1]))  # 转为 [(x, y), (x, y), ...]

                if match_points:
                    print(f"【{step_name}】，全屏匹配到 {len(match_points)} 处")
                    logging.info(f"【{step_name}】，全屏匹配到 {len(match_points)} 处")
                    if len(match_points) > 1:
                        print(f"【{step_name}】，已合并匹配到的区域")
                        logging.info(f"【{step_name}】，已合并匹配到的区域")

                    # 模板尺寸
                    th, tw = template.shape[:2]

                    # 合并所有匹配区域
                    x1_all = min([pt[0] for pt in match_points])
                    y1_all = min([pt[1] for pt in match_points])
                    x2_all = max([pt[0] + tw for pt in match_points])
                    y2_all = max([pt[1] + th for pt in match_points])

                    # 向四周扩展 20 像素，限制边界不越界
                    x1_new = max(0, x1_all - 20)
                    y1_new = max(0, y1_all - 20)
                    x2_new = min(screenshot.shape[1], x2_all + 20)
                    y2_new = min(screenshot.shape[0], y2_all + 20)

                    recognition_area = f"{x1_new},{y1_new},{x2_new},{y2_new}"
                    img_area = recognition_area
                    area_choice_value = 'screenshot'
                    new_area_str = f"{recognition_area}|{area_choice_value}|{img_area}"

                    # 更新当前步骤的识别区域
                    new_image = list(current_step)
                    new_image[14] = new_area_str
                    step_name = new_image[1]
                    self.image_list[selected_index] = tuple(new_image)
                
                self.update_image_listbox()

                print(f"【{step_name}】识图区域更新为({img_area})")
                logging.info(f"【{step_name}】识图区域更新为({img_area})")
            
            # 先处理鼠标点击、滚轮操作等
            if mouse_coordinates and not self.only_keyboard_var.get():
                try:
                    if ":" in mouse_coordinates:
                        parts = mouse_coordinates.split(":")
                        action = parts[0]
                        
                        # 如果是无操作，直接跳过不执行任何鼠标动作
                        if action == "none":
                            pass  # 不执行任何操作
                        else:
                            coords = parts[1]
                            is_dynamic = parts[2]
                            # 对于需要计数的操作（点击、滚轮），解析最后的数字，默认 1
                            count_val = int(parts[3]) if len(parts) > 3 else 1  

                            # 计算动态点击的位置
                            if is_dynamic == "1":
                                x = max_loc[0] + template.shape[1] // 2 + x1
                                y = max_loc[1] + template.shape[0] // 2 + y1
                            else:
                                x, y = map(int, coords.split(","))

                            # 执行相应的鼠标操作
                            if action == "click":
                                for _ in range(count_val):
                                    pyautogui.click(x, y)
                            elif action == "rightClick":
                                pyautogui.moveTo(x, y)
                                pyautogui.rightClick()
                            elif action == "doubleClick":
                                pyautogui.doubleClick(x, y)
                            elif action == "mouseDown":
                                pyautogui.mouseDown(x, y)
                            elif action == "mouseUp":
                                pyautogui.mouseUp(x, y)
                            elif action == "scrollUp":
                                # 移动到坐标后，再执行滚轮操作
                                pyautogui.moveTo(x, y)
                                # 循环 count_val 次，每次滚动 70 行（正值表示向上滚动）
                                for _ in range(count_val):
                                    pyautogui.scroll(70, x=x, y=y)
                            elif action == "scrollDown":
                                # 移动到坐标后，再执行滚轮操作
                                pyautogui.moveTo(x, y)
                                # 循环 count_val 次，每次滚动 70 行（调用时转换为负值表示向下滚动）
                                for _ in range(count_val):
                                    pyautogui.scroll(-70, x=x, y=y)
                    else:
                        # 处理旧格式的坐标（向后兼容）
                        x, y = map(int, mouse_coordinates.split(','))
                        pyautogui.click(x, y)
                except Exception as e:
                    print(f"【{step_name}】，操作执行出错: {e}")
                    print(f"【{step_name}】，执行鼠标操作：{mouse_coordinates}")
                    logging.info(f"【{step_name}】，执行鼠标操作：{mouse_coordinates}")
                    return False
                
            # 再处理键盘动作
            if keyboard_input:
                try:      
                    print(f"[DEBUG] 解析输入: {keyboard_input}")
                    commands = self.parse_keyboard_input(keyboard_input)

                    for cmd in commands:
                        print(f"[DEBUG] 执行命令: {cmd}")
                        if isinstance(cmd, tuple) and cmd[0] == "hotkey":
                            keys = cmd[1]
                            print(f"[DEBUG] 发送组合键: {keys}")
                            pyautogui.hotkey(*keys)
                        elif isinstance(cmd, float):  # 延时
                            print(f"[DEBUG] 延时 {cmd} 秒")
                            time.sleep(cmd)
                        elif isinstance(cmd, tuple) and cmd[0] == "text":  # 纯文本粘贴
                            print(f"[DEBUG] 纯文本粘贴: {cmd[1]}")
                            # 保存原有剪贴板内容
                            original_clipboard = pyperclip.paste()  
                            # 将待粘贴内容复制到剪贴板
                            pyperclip.copy(cmd[1])
                            time.sleep(0.1)  # 等待剪贴板更新
                            pyautogui.hotkey("ctrl", "v")  # 执行粘贴
                            time.sleep(0.1)  # 粘贴操作后等待确保内容完成传输
                            # 恢复原有剪贴板内容
                            pyperclip.copy(original_clipboard)
                            print("[DEBUG] 剪贴板内容已恢复")
                        else:  # 普通按键
                            print(f"[DEBUG] 发送按键: {cmd}")
                            pyautogui.press(cmd)
                        
                        time.sleep(0.1)  # 按键间短暂延时

                    print(f"[INFO] 执行完成:【{step_name}】， {keyboard_input}")
                except Exception as e:
                    print(f"[ERROR]【{step_name}】， 键盘动作时出错: {e}")

            return True
        else:
            print(f"【{step_name}】，最大相似度：{max_val:.1f}，期望相似度：{similarity_threshold}，执行重新匹配")
            logging.info(f"【{step_name}】，最大相似度：{max_val:.1f}，期望相似度：{similarity_threshold}，执行重新匹配")
            return False
   
    def parse_keyboard_input(self, input_str):
        """解析键盘动作字符串，返回命令列表（调试版）"""
        commands = []
        i = 0
        buffer = ""  # 用于收集普通文本

        print(f"[DEBUG] 开始解析输入: {input_str}")

        while i < len(input_str):
            if input_str[i] == '{':
                # 先把缓冲区的普通文本加入命令列表
                if buffer:
                    print(f"[DEBUG] 添加纯文本: {buffer}")
                    commands.append(("text", buffer))
                    buffer = ""

                end = input_str.find('}', i)
                if end != -1:
                    cmd = input_str[i+1:end]
                    print(f"[DEBUG] 解析到命令: {cmd}")

                    if cmd.startswith('delay:'):
                        # 处理延时命令
                        try:
                            delay_ms = int(cmd.split(':')[1])
                            delay_sec = float(delay_ms / 1000)
                            print(f"[DEBUG] 添加延时: {delay_sec} 秒")
                            commands.append(delay_sec)
                        except ValueError:
                            print(f"[ERROR] 无效的延时值: {cmd}")
                    elif '+' in cmd:
                        # 处理组合键
                        keys = cmd.split('+')
                        print(f"[DEBUG] 添加组合键: {keys}")
                        commands.append(("hotkey", tuple(keys)))
                    else:
                        # 处理特殊键
                        print(f"[DEBUG] 添加特殊键: {cmd}")
                        commands.append(cmd)
                    i = end + 1
                    continue
            else:
                # 普通字符加入缓冲区
                buffer += input_str[i]
            i += 1

        # 处理最后一段普通文本
        if buffer:
            print(f"[DEBUG] 添加结尾纯文本: {buffer}")
            commands.append(("text", buffer))

        print(f"[DEBUG] 最终解析的命令: {commands}")
        return commands

 
    def add_special_key(self, key):
        current_entry = self.entry.get()
        self.entry.delete(0, tk.END)
        self.entry.insert(0, current_entry + key)
   
    def edit_keyboard_input(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]

            # 创建新窗口
            dialog = tk.Toplevel(self.root)
            dialog.withdraw()                     # 先隐藏
            dialog.title("设置键盘操作")
            dialog.transient(self.root)
            dialog.grab_set()
                
            # 创建输入框和标签
            input_frame = tk.Frame(dialog)
            input_frame.pack(fill=tk.X, pady=5)
            tk.Label(input_frame, text="键盘动作:").pack(side=tk.LEFT)
            entry = tk.Entry(input_frame, width=30)
            entry.insert(0, selected_image[3])
            entry.pack(side=tk.LEFT, padx=5)

            # 创建特殊键按钮框架
            special_keys_frame = tk.LabelFrame(dialog, text="特殊键", padx=5, pady=5)
            special_keys_frame.pack(fill=tk.X, pady=5)

            special_keys = [
                'enter', 'tab', 'space', 'backspace', 'delete',
                'esc', 'home', 'end', 'pageup', 'pagedown',
                'up', 'down', 'left', 'right'
            ]

            # 创建特殊键按钮（使用ttk.Button和secondary-outline样式）
            for i, key in enumerate(special_keys):
                btn = ttk.Button(
                    special_keys_frame, 
                    text=key.upper(),
                    command=lambda k=key: add_special_key(f"{{{k}}}"),
                    bootstyle="secondary-outline"
                )
                btn.grid(row=i//7, column=i%7, padx=2, pady=2, sticky='ew')

            # 创建组合键框架
            combo_keys_frame = tk.LabelFrame(dialog, text="组合键", padx=5, pady=5)
            combo_keys_frame.pack(fill=tk.X, pady=5)

            # 创建常用组合键按钮
            combo_keys = [
                ('复制', 'ctrl+c'), ('粘贴', 'ctrl+v'), ('剪切', 'ctrl+x'),
                ('全选', 'ctrl+a'), ('保存', 'ctrl+s'), ('撤销', 'ctrl+z')
            ]

            for i, (name, combo) in enumerate(combo_keys):
                btn = ttk.Button(
                    combo_keys_frame, 
                    text=name,
                    command=lambda c=combo: add_special_key(f"{{{c}}}"),
                    bootstyle="secondary-outline"
                )
                btn.grid(row=i//3, column=i%3, padx=2, pady=2, sticky='ew')

            # 创建修饰键框架
            modifier_keys_frame = tk.LabelFrame(dialog, text="修饰键", padx=5, pady=5)
            modifier_keys_frame.pack(fill=tk.X, pady=5)

            modifier_keys = ['ctrl', 'alt', 'shift', 'win']
            for i, key in enumerate(modifier_keys):
                btn = ttk.Button(
                    modifier_keys_frame, 
                    text=key.upper(),
                    command=lambda k=key: add_special_key(f"{{{k}}}"),
                    bootstyle="secondary-outline"
                )
                btn.grid(row=0, column=i, padx=2, pady=2, sticky='ew')

            # 创建功能键框架
            function_keys_frame = tk.LabelFrame(dialog, text="功能键", padx=5, pady=5)
            function_keys_frame.pack(fill=tk.X, pady=5)

            for i in range(12):
                btn = ttk.Button(
                    function_keys_frame, 
                    text=f"F{i+1}",
                    command=lambda k=i+1: add_special_key(f"{{f{k}}}"),
                    bootstyle="secondary-outline"
                )
                btn.grid(row=i//6, column=i%6, padx=2, pady=2, sticky='ew')

            def add_special_key(key):
                current_pos = entry.index(tk.INSERT)
                entry.insert(current_pos, key)
                entry.focus_set()

            def save_input():
                new_keyboard_input = entry.get().strip()
                tpl = tuple(selected_image)
                new_image = tpl[:3] + (new_keyboard_input,) + tpl[4:]
                self.image_list[selected_index] = new_image
                self.update_image_listbox()
                dialog.destroy()
            
            # 添加保存和取消按钮
            button_frame = tk.Frame(dialog)
            button_frame.pack(fill=tk.X, pady=10)

            # 在创建按钮时添加bootstyle参数
            save_button = ttk.Button(
                button_frame, 
                text="保存", 
                command=save_input,
                bootstyle="primary-outline"  # 主要轮廓样式
            )
            save_button.pack(side=tk.RIGHT, padx=5)

            cancel_button = ttk.Button(
                button_frame, 
                text="取消", 
                command=dialog.destroy,
                bootstyle="primary-outline"  # 次要轮廓样式
            )
            cancel_button.pack(side=tk.RIGHT, padx=5)

            # 让 Tkinter 计算理想大小
            dialog.update_idletasks()
            w = dialog.winfo_reqwidth()
            h = dialog.winfo_reqheight()

            # 计算居中位置
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_w = self.root.winfo_width()
            main_h = self.root.winfo_height()
            x = main_x + (main_w - w) // 2
            y = main_y + (main_h - h) // 2

            # 一次性设置大小和位置，并显示
            dialog.geometry(f"{w}x{h}+{x}+{y}")
            dialog.deiconify()

            dialog.iconbitmap("icon/app.ico")

    def edit_mouse_action(self):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        # 创建对话框
        dialog = tk.Toplevel(self.root)
        dialog.withdraw()                     # 先隐藏
        dialog.title("设置鼠标操作")
        dialog.transient(self.root)
        dialog.grab_set()

        # 解析现有的鼠标操作数据
        current_action = "click"
        current_coords = ""
        current_dynamic = False
        current_count = "1"

        if selected_image[4]:  # 如果有现有的鼠标操作数据
            try:
                parts = selected_image[4].split(":")
                if len(parts) >= 3:
                    current_action = parts[0]
                    current_coords = parts[1]
                    current_dynamic = parts[2] == "1"
                    if current_action in ["click", "scrollUp", "scrollDown"] and len(parts) == 4:
                        current_count = parts[3]
                if len(parts) >= 2:
                    current_action = parts[0]
                    current_coords = parts[1]
                else:
                    current_coords = selected_image[4]
            except:
                pass

        # 创建坐标输入框
        coord_frame = tk.Frame(dialog)
        coord_frame.pack(fill=tk.X, pady=5)
        tk.Label(coord_frame, text="坐标 (x,y):").pack(side=tk.LEFT)
        coord_entry = tk.Entry(coord_frame, width=20)
        coord_entry.insert(0, current_coords)
        coord_entry.pack(side=tk.LEFT, padx=5)

        # 创建鼠标动作选择框架
        action_frame = tk.LabelFrame(dialog, text="鼠标动作", padx=5, pady=5)
        action_frame.pack(fill=tk.X, pady=5)

        # 鼠标动作类型
        action_var = tk.StringVar(value=current_action)
        actions = [
            ("左键单击", "click"),
            ("右键单击", "rightClick"),
            ("双击", "doubleClick"),
            ("按住", "mouseDown"),
            ("释放", "mouseUp")
        ]

        # 用于存储【左键单击】旁边的循环次数输入框引用
        left_click_entry = None

        for text, value in actions:
            if value == "click":
                frame = tk.Frame(action_frame)
                frame.pack(anchor=tk.W)
                tk.Radiobutton(frame, value=value, text=text, variable=action_var).pack(side=tk.LEFT)
                left_click_entry = tk.Entry(frame, width=5)
                left_click_entry.insert(0, current_count if current_action=="click" else "1")
                left_click_entry.pack(side=tk.LEFT, padx=5)
                tk.Label(frame, text="次").pack(side=tk.LEFT)
            else:
                tk.Radiobutton(action_frame, text=text, value=value, variable=action_var).pack(anchor=tk.W)

        # 滚轮向上操作
        frame_scroll_up = tk.Frame(action_frame)
        frame_scroll_up.pack(anchor=tk.W)
        tk.Radiobutton(frame_scroll_up, value="scrollUp", text="滚轮向上", variable=action_var).pack(side=tk.LEFT)
        scroll_up_entry = tk.Entry(frame_scroll_up, width=5)
        scroll_up_entry.insert(0, current_count if current_action=="scrollUp" else "1")
        scroll_up_entry.pack(side=tk.LEFT, padx=5)
        tk.Label(frame_scroll_up, text="行").pack(side=tk.LEFT)

        # 滚轮向下操作
        frame_scroll_down = tk.Frame(action_frame)
        frame_scroll_down.pack(anchor=tk.W)
        tk.Radiobutton(frame_scroll_down, value="scrollDown", text="滚轮向下", variable=action_var).pack(side=tk.LEFT)
        scroll_down_entry = tk.Entry(frame_scroll_down, width=5)
        scroll_down_entry.insert(0, current_count if current_action=="scrollDown" else "1")
        scroll_down_entry.pack(side=tk.LEFT, padx=5)
        tk.Label(frame_scroll_down, text="行").pack(side=tk.LEFT)

        # 添加无操作选项
        tk.Radiobutton(action_frame, value="none", text="无操作", variable=action_var).pack(anchor=tk.W)

        # 动态点击勾选框
        dynamic_var = tk.BooleanVar(value=current_dynamic)
        tk.Checkbutton(action_frame, text="动态点击", variable=dynamic_var).pack(anchor=tk.W)

        def save_mouse_action():
            try:
                # 获取坐标
                coords = coord_entry.get().strip()
                if not coords or "," not in coords:  # 无操作也需要坐标验证
                    messagebox.showerror("错误", "请输入有效的坐标 (x,y)", parent=dialog)
                    return
                    
                try:
                    x, y = map(int, coords.split(","))  # 验证坐标是否为整数
                except ValueError:
                    messagebox.showerror("错误", "坐标必须是整数", parent=dialog)
                    return

                action = action_var.get()
                
                if action == "none":
                    # 无操作模式：只保留坐标
                    mouse_action = f"{action}:{coords}"
                    mouse_action_result = ""  # 显示为空
                else:
                    dynamic = "1" if dynamic_var.get() else "0"

                    # 获取次数/行数
                    if action == "click":
                        count_str = left_click_entry.get().strip() if left_click_entry else "1"
                    elif action in ["scrollUp", "scrollDown"]:
                        count_str = scroll_up_entry.get().strip() if action == "scrollUp" else scroll_down_entry.get().strip()
                    else:
                        count_str = "1"

                    try:
                        count_val = int(count_str)
                        if count_val < 1:
                            raise ValueError
                    except ValueError:
                        messagebox.showerror("错误", "请输入有效的次数/行数（正整数）", parent=dialog)
                        return

                    # 生成标准格式
                    if action in ["click", "scrollUp", "scrollDown"]:
                        mouse_action = f"{action}:{coords}:{dynamic}:{count_val}"
                    else:
                        mouse_action = f"{action}:{coords}:{dynamic}"

                    # 生成可读描述
                    action_mapping = {
                        "click": "左键单击",
                        "rightClick": "右键单击",
                        "doubleClick": "双击",
                        "mouseDown": "按住",
                        "mouseUp": "释放",
                        "scrollUp": "向上滚动",
                        "scrollDown": "向下滚动"
                    }
                    action_desc = action_mapping.get(action, action)
                    dynamic_desc = " 启用动态点击" if dynamic == "1" else ""
                    unit = "行" if action in ["scrollUp", "scrollDown"] else "次"
                    
                    mouse_action_result = f"{action_desc} {count_val}{unit}{dynamic_desc}" if action in ["click", "scrollUp", "scrollDown"] \
                                        else f"{action_desc}{dynamic_desc}"

                # 更新数据
                tpl = tuple(selected_image)
                # 修改索引4和10：
                # tpl[:4] 是前4个元素 (0,1,2,3)
                # tpl[5:10] 是元素5到9
                # tpl[11:] 是元素11到末尾
                new_image = tpl[:4] + (mouse_action,) + tpl[5:10] + (mouse_action_result,) + tpl[11:]
                self.image_list[selected_index] = new_image

                self.update_image_listbox()
                dialog.destroy()

            except Exception as e:
                messagebox.showerror("错误", f"保存时出错: {str(e)}", parent=dialog)

        # 添加保存和取消按钮
        button_frame = tk.Frame(dialog)
        button_frame.pack(fill=tk.X, pady=10)

        # 在创建按钮时添加bootstyle参数
        save_button = ttk.Button(
            button_frame, 
            text="保存", 
            command=save_mouse_action,
            bootstyle="primary-outline"  
        )
        save_button.pack(side=tk.RIGHT, padx=5)

        cancel_button = ttk.Button(
            button_frame, 
            text="取消", 
            command=dialog.destroy,
            bootstyle="primary-outline"  
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)

        # 让 Tkinter 计算理想大小
        dialog.update_idletasks()
        w = dialog.winfo_reqwidth()
        h = dialog.winfo_reqheight()

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - w) // 2
        y = main_y + (main_h - h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{w}x{h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")

    def offset_coords(self):
        
        # 获取当前屏幕分辨率
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        self.get_screen_scale()

        dialog = tk.Toplevel(self.root)
        dialog.withdraw()                     # 先隐藏
        dialog.title("设置偏移量")
        dialog.transient(self.root)
        dialog.grab_set()

        # 创建输入框
        input_frame = tk.Frame(dialog)
        input_frame.pack(pady=10)

        tk.Label(input_frame, text="X:").grid(row=0, column=0, padx=(10,0), pady=(20,0), sticky='e')
        x_entry = tk.Entry(input_frame, width=5)
        x_entry.insert(0, "0")
        x_entry.grid(row=0, column=1, padx=(0,0), pady=(20,0))

        tk.Label(input_frame, text="Y:").grid(row=0, column=2, padx=(5,0), pady=(20,0), sticky='e')
        y_entry = tk.Entry(input_frame, width=5)
        y_entry.insert(0, "0")
        y_entry.grid(row=0, column=3, padx=(0,10), pady=(20,0))

        # 存储要偏移的步骤索引
        selected_indices = []

        def select_steps():
            sel_dialog = tk.Toplevel(dialog)
            sel_dialog.withdraw()  # 先隐藏窗口
            sel_dialog.title("选择更多步骤")
            sel_dialog.transient(dialog)
            sel_dialog.grab_set()

            # 获取初始选中的索引（来自 selected_indices 或 Treeview 当前选中项）
            if selected_indices:
                initial = set(selected_indices)
            else:
                initial = {self.tree.index(sel) for sel in self.tree.selection()}

            # 列表框及滚动条
            list_frame = tk.Frame(sel_dialog)
            list_frame.pack(padx=10, pady=(10, 0), fill='both', expand=True)

            scrollbar = tk.Scrollbar(list_frame, orient='vertical')
            listbox = tk.Listbox(list_frame, selectmode='multiple', yscrollcommand=scrollbar.set)
            scrollbar.config(command=listbox.yview)
            scrollbar.pack(side='right', fill='y')
            listbox.pack(side='left', fill='both', expand=True)

            # 支持 Shift 范围选择
            # 设置初始选中项（对应 Treeview 的选中项）
            for idx in initial:
                listbox.selection_set(idx)

            # 记录初始索引（Treeview 的第一个选中项）
            initial_index = next(iter(initial)) if initial else None
            last_click = {'index': initial_index}

            def on_click(event):
                idx = listbox.nearest(event.y)
                shift_pressed = (event.state & 0x0001) != 0  # 检测是否按住 Shift

                if shift_pressed and last_click['index'] is not None:
                    # 判断当前点击位置是在初始索引的左边还是右边
                    if idx < last_click['index']:
                        # 只能选择左边（从 idx 到 initial_index）
                        listbox.selection_clear(0, tk.END)  # 先清空所有选择
                        listbox.selection_set(idx, last_click['index'])
                    else:
                        # 只能选择右边（从 initial_index 到 idx）
                        listbox.selection_clear(0, tk.END)
                        listbox.selection_set(last_click['index'], idx)
                else:
                    # 普通点击：切换选中状态
                    if listbox.selection_includes(idx):
                        listbox.selection_clear(idx)
                    else:
                        listbox.selection_set(idx)
                    last_click['index'] = idx  # 更新最后点击的索引
                return "break"

            listbox.bind('<Button-1>', on_click)

            # 插入步骤
            for idx, image in enumerate(self.image_list):
                listbox.insert('end', image[1])
                if idx in initial:
                    listbox.selection_set(idx)

            # 如果有选中的项目，滚动到第一个选中的项目上方两行
            if initial:
                first_selected = min(initial)
                # 计算向上偏移2行的位置（最小为0）
                scroll_pos = max(0, first_selected - 2)
                listbox.see(scroll_pos)

            # 全选复选框
            all_var = tk.BooleanVar(value=False)
            def toggle_all():
                if all_var.get():
                    listbox.select_set(0, 'end')
                else:
                    listbox.select_clear(0, 'end')
            all_check = ttk.Checkbutton(sel_dialog, text="全选", variable=all_var, command=toggle_all, bootstyle="secondary")
            all_check.pack(anchor='w', padx=10, pady=(5, 0))

            # 应用/取消按钮区域
            btn_frame2 = tk.Frame(sel_dialog)
            btn_frame2.pack(pady=10, fill='x')
            ok_btn = ttk.Button(btn_frame2, text="应用", command=lambda: (set_selected(), sel_dialog.destroy()), bootstyle="primary-outline")
            ok_btn.pack(side=tk.RIGHT, padx=5)
            cancel_btn = ttk.Button(btn_frame2, text="取消", command=sel_dialog.destroy, bootstyle="primary-outline")
            cancel_btn.pack(side=tk.RIGHT)

            def set_selected():
                nonlocal selected_indices
                selected_indices = list(listbox.curselection())

            # 居中对话框
            sel_dialog.update_idletasks()
            pw, ph = dialog.winfo_width(), dialog.winfo_height()
            px, py = dialog.winfo_x(), dialog.winfo_y()
            w, h = sel_dialog.winfo_width(), sel_dialog.winfo_height()
            sel_dialog.geometry(f"{w}x{h}+{px + (pw - w) // 2}+{py + (ph - h) // 2}")

            sel_dialog.iconbitmap("icon/app.ico")
            sel_dialog.deiconify()  # 一次性显示在正确位置

        def on_save():
            try:
                offset_x = int(x_entry.get())
                offset_y = int(y_entry.get())
            except ValueError:
                messagebox.showerror("错误", "请输入有效的整数偏移量。")
                return

            def process_mouse_info(mouse_info):
                current_action, current_coords, current_dynamic, current_count = "click", "", False, "1"
                if mouse_info:
                    parts = mouse_info.split(":")
                    if len(parts) >= 3:
                        current_action, current_coords = parts[0], parts[1]
                        current_dynamic = parts[2] == "1"
                        if current_action in ["click","scrollUp","scrollDown"] and len(parts) == 4:
                            current_count = parts[3]
                    else:
                        current_coords = mouse_info
                try:
                    x, y = map(int, current_coords.split(","))
                    new_x, new_y = x + offset_x, y + offset_y
                    if new_x < 0 or new_y < 0: return "NEGATIVE"
                    if new_x > screen_width or new_y > screen_height: return "OUT_OF_BOUNDS"
                except:
                    return None
                new_info = f"{current_action}:{new_x},{new_y}:{'1' if current_dynamic else '0'}"
                if current_action in ["click","scrollUp","scrollDown"]:
                    new_info += f":{current_count}"
                return new_info

            targets = selected_indices or ([self.tree.index(item) for item in self.tree.selection()] if self.tree.selection() else [])
            if not targets:
                return

            for i in targets:
                image = self.image_list[i]
                new_info = process_mouse_info(image[4])
                if new_info == "NEGATIVE":
                    messagebox.showerror("错误", "偏移结果存在负坐标，请重新设置偏移量。")
                    return
                if new_info == "OUT_OF_BOUNDS":
                    messagebox.showerror("错误", f"偏移结果超出屏幕范围({screen_width}x{screen_height})，请重新设置偏移量。")
                    return
                if new_info:
                    self.image_list[i] = (*image[:4], new_info, *image[5:])
                    old_coodr = image[4].split(":")[1] if image[4] and ":" in image[4] else image[4]
                    new_coodr = new_info.split(":")[1] if new_info and ":" in new_info else new_info
                    step_name = image[1]
                    logging.info(f"【{step_name}】坐标更新：({old_coodr}) → ({new_coodr})")      
                    print(f"【{step_name}】坐标更新：({old_coodr}) → ({new_coodr})")

            self.update_image_listbox()
            dialog.destroy()

        # 按钮框架
        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=10)

        # 第一行：单独一个“应用于更多步骤”按钮
        apply_btn = ttk.Button(
            btn_frame,
            text="应用于更多步骤",
            command=select_steps,  # 你的处理函数
            bootstyle="primary-outline"
        )
        apply_btn.grid(row=0, column=0, padx=5, pady=5, sticky="ew")  # 关键：sticky="ew" 让按钮填满宽度

        # 第二行：一个子Frame，承载“取消”“保存”两个按钮
        sub_frame = tk.Frame(btn_frame)
        sub_frame.grid(row=1, column=0, pady=5, sticky="ew")  # 关键：sticky="ew" 让子Frame填满宽度

        cancel_btn = ttk.Button(
            sub_frame,
            text="取消",
            command=dialog.destroy,
            bootstyle="primary-outline"
        )
        cancel_btn.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)  # 关键：expand=True 让按钮平分宽度

        save_btn = ttk.Button(
            sub_frame,
            text="保存",
            command=on_save,
            bootstyle="primary-outline"
        )
        save_btn.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)  # 关键：expand=True 让按钮平分宽度

        # 关键：让 btn_frame 的列0自动扩展
        btn_frame.grid_columnconfigure(0, weight=1)

        # 让 Tkinter 计算理想大小
        dialog.update_idletasks()
        w = dialog.winfo_reqwidth()
        h = dialog.winfo_reqheight()

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - w) // 2
        y = main_y + (main_h - h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{w}x{h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")

    def save_config(self):
        # 构造配置字典，过滤掉不存在的图片
        self.loop_count = int(self.loop_count_entry.get())
        config = {
            'hotkey': self.hotkey,
            'similarity_threshold': self.similarity_threshold,
            'delay_time': self.delay_time,
            'loop_count': self.loop_count,
            'image_list': [img for img in self.image_list if os.path.exists(img[0])],
            'only_keyboard': self.only_keyboard_var.get(),
        }
        # 检查图片列表是否为空
        if not config['image_list']:
            response = messagebox.askyesno(
                "警告", 
                "当前没有可保存的图片步骤，是否继续保存配置？", 
                parent=self.root
            )
            if not response:
                return  # 用户选择不继续

        # 创建居中对话框获取配置文件名
        dialog = tk.Toplevel(self.root)
        dialog.withdraw()                     # 先隐藏
        dialog.title("保存配置")
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text="保存名称:").pack(padx=10, pady=5)
        
        # 创建输入框并设置默认值为当前配置文件名（如果有的话）
        entry = tk.Entry(dialog, width=30)
        if hasattr(self, 'config_filename') and self.config_filename:
            # 只显示文件名，不带路径和扩展名
            default_name = os.path.splitext(os.path.basename(self.config_filename))[0]
            entry.insert(0, default_name)
        entry.pack(padx=10, pady=5)
        entry.focus_set()

        def on_ok():
            nonlocal filename
            filename = entry.get().strip()
            if not filename:
                messagebox.showwarning("警告", "请输入配置文件名", parent=dialog)
                return
            if not filename.endswith('.json'):
                filename += '.json'
            
            # 检查文件是否存在
            if os.path.exists(filename):
                # 询问是否覆盖
                response = messagebox.askyesno("确认", "配置文件已存在，是否覆盖保存？", parent=dialog)
                if not response:  # 如果用户选择不覆盖
                    return  # 不执行后续操作
            
            dialog.destroy()

        def on_cancel():
            nonlocal filename
            filename = None
            dialog.destroy()

        filename = None
        button_frame = tk.Frame(dialog)
        button_frame.pack(pady=5)

        # 在创建按钮时添加bootstyle参数
        save_button = ttk.Button(
            button_frame, 
            text="保存", 
            command=on_ok,
            bootstyle="primary-outline"  
        )
        save_button.pack(side=tk.RIGHT, padx=5)

        cancel_button = ttk.Button(
            button_frame, 
            text="取消", 
            command=on_cancel,
            bootstyle="primary-outline"  
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)

        # 让 Tkinter 计算理想大小
        dialog.update_idletasks()
        w = dialog.winfo_reqwidth()
        h = dialog.winfo_reqheight()

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - w) // 2
        y = main_y + (main_h - h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{w}x{h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")

        self.root.wait_window(dialog)

        if not filename:
            return

        try:
            # 获取程序工作目录
            working_dir = os.getcwd()
            config_path = os.path.join(working_dir, filename)          
            screenshots_dir = self.screenshot_folder

            # 创建与配置同名的子文件夹
            config_basename = os.path.splitext(os.path.basename(filename))[0]
            new_folder_path = os.path.join(screenshots_dir, config_basename)
            os.makedirs(new_folder_path, exist_ok=True)

            # 复制图片到新文件夹并更新路径
            updated_image_list = []
            for img_data in config['image_list']:
                old_path = img_data[0]
                new_path = os.path.join(new_folder_path, os.path.basename(old_path))
                
                # 如果新旧路径相同，则跳过复制
                if os.path.abspath(old_path) == os.path.abspath(new_path):
                    new_img_data = (old_path,) + tuple(img_data[1:])  # 直接使用原路径
                    updated_image_list.append(new_img_data)
                    continue  # 跳过后续复制操作
                
                try:
                    shutil.copy2(old_path, new_path)
                    logging.info(f"图片复制成功: {old_path} -> {new_path}")
                except Exception as copy_err:
                    logging.error(f"复制图片 {old_path} 时出错: {copy_err}")
                    new_path = old_path  # 复制失败则回退到原路径

                new_img_data = (new_path,) + tuple(img_data[1:])
                updated_image_list.append(new_img_data)

            config['image_list'] = updated_image_list
            
            # 保存配置文件
            with open(config_path, 'w', encoding='utf-8') as f:
                json.dump(config, f, ensure_ascii=False, indent=4)       
            self.config_filename = config_path
    
            # 简化保存成功提示
            messagebox.showinfo("保存成功", "配置保存成功！", parent=self.root)
            self.image_list = updated_image_list
            self.update_label()
            
        except Exception as e:
            error_msg = f"保存配置时出错: {str(e)}"
            logging.error(error_msg)
            messagebox.showerror("保存失败", error_msg, parent=self.root)
   
    def load_config(self):

        # 获取程序工作目录
        working_dir = os.getcwd()

        # 查找所有.json配置文件
        config_files = [f for f in os.listdir(working_dir) if f.endswith('.json') and f != 'last_config.json']

        if not config_files:
            messagebox.showinfo("提示", "没有找到任何配置文件", parent=self.root)
            return False

        # 创建居中对话框显示配置文件列表   
        dialog = tk.Toplevel(self.root)
        dialog.withdraw()                     # 先隐藏
        dialog.title("选择配置文件加载")
        dialog.transient(self.root)
        dialog.grab_set()

        # 主容器框架
        main_frame = tk.Frame(dialog)
        main_frame.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)

        # 搜索框区域
        style = tb.Style()  
        style.configure("Border.TFrame", background="#ced4da")
        style.configure("InnerR.TFrame", background="white")
        border_width = 1

        # 外层 Frame 模拟边框
        search_border = tb.Frame(main_frame)
        search_border.pack(fill=tk.X, expand=True, padx=0, pady=5)
        search_border.configure(style="Border.TFrame")

        # 内层 Frame 白底（必须使用 bootstyle="light"）
        search_inner = tb.Frame(
            search_border, 
            bootstyle="light",
            style="InnerR.TFrame"
        )
        search_inner.pack(fill=tk.X, expand=True, padx=border_width, pady=border_width)

        search_var = tk.StringVar()
        # 定义所有状态下的边框颜色为白色
        style.map(
            'White.TEntry',
            bordercolor=[
                ('active', 'white'),    # 鼠标悬停/激活状态
                ('focus', 'white'),     # 获取焦点状态
                ('disabled', 'white'),  # 禁用状态
                ('!disabled', 'white')  # 默认状态
            ],
            lightcolor=[('', 'white')],  # 未选中时的边框高亮
            darkcolor=[('', 'white')]    # 阴影颜色
        )
        # 配置基础样式
        style.configure(
            'White.TEntry',
            foreground='black',          # 文字颜色
            fieldbackground='white',     # 背景色
            borderwidth=1               # 边框宽度
        )
        # 创建并应用 Entry
        search_var = tk.StringVar()
        entry = Entry(
            search_inner,
            textvariable=search_var,
            style='White.TEntry',
        )
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 0), pady=0)

        # 图标
        img = Image.open("icon/search.png").resize((16, 16), Image.Resampling.LANCZOS)
        search_icon = ImageTk.PhotoImage(img)

        icon_label = tk.Label(search_inner, image=search_icon, bg="white", bd=0)
        icon_label.image = search_icon  # 防止被垃圾回收
        icon_label.pack(side=tk.RIGHT, padx=5)

        placeholder_original = "在加载配置中搜索"
        placeholder = f"{placeholder_original}"  # 统一使用这个变量

        def set_placeholder():
            entry.delete(0, tk.END)
            entry.insert(0, placeholder)
            entry.config(foreground='grey')

        def clear_placeholder(event=None):
            if entry.get() == placeholder:
                entry.delete(0, tk.END)
                entry.config(foreground='black')

        def restore_placeholder(event=None):
            if not entry.get():
                set_placeholder()
                
        def on_search(*args):
            text = search_var.get().strip()
            if text == "" or text == placeholder_original:
                update_listbox("")  # 显示所有
            else:
                update_listbox(text)

        # 初始化 placeholder
        set_placeholder()

        # 事件绑定
        entry.bind("<FocusIn>", clear_placeholder)
        entry.bind("<FocusOut>", restore_placeholder)
        search_var.trace_add('write', on_search)

        # 列表框容器
        list_container = tk.Frame(main_frame)
        list_container.pack(fill=tk.BOTH, expand=True)

        # 列表框和滚动条
        listbox = tk.Listbox(list_container, selectmode=tk.SINGLE)
        scrollbar = tk.Scrollbar(list_container)
        scrollbar.config(command=listbox.yview)
        listbox.config(yscrollcommand=scrollbar.set)

        # 获取当前已加载的配置文件名（如果有）
        current_loaded = os.path.basename(self.config_filename) if hasattr(self, 'config_filename') and self.config_filename else None
        # 保存原始文件列表
        self.original_config_files = config_files

        def update_listbox(filter_text=""):
            listbox.delete(0, tk.END)
            for config_file in self.original_config_files:
                if filter_text.lower() in config_file.lower():
                    display_name = config_file
                    if current_loaded and config_file == current_loaded:
                        display_name = f"{config_file} (当前配置)"
                    listbox.insert(tk.END, display_name)

        update_listbox()
        # 绑定双击事件
        # 先定义一个判断点击是否在 item 上的函数（可复用之前的 index_at_event）
        def index_at_event(event):
            idx = listbox.nearest(event.y)
            bbox = listbox.bbox(idx)
            if bbox:
                x, y, w, h = bbox
                if y <= event.y <= y + h:
                    return idx
            return None

        # 双击回调：先判断是否点在有效行上，再调用 edit_config_name
        def on_double_click(event):
            idx = index_at_event(event)
            if idx is None:
                return  # 点击空白，直接返回
            # 选中该行（可选，edit_config_name 内部也会检查 selection）
            listbox.selection_clear(0, tk.END)
            listbox.selection_set(idx)
            listbox.activate(idx)
            # 这里正确传递 dialog，而不是 event
            self.edit_config_name(dialog, listbox, working_dir, event)

        # 绑定时，不要把 event 误传为 dialog
        listbox.bind("<Double-Button-1>", on_double_click)

        # 使用grid布局让列表框和滚动条并排
        listbox.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")

        # 配置grid权重
        list_container.grid_rowconfigure(0, weight=1)
        list_container.grid_columnconfigure(0, weight=1)

        # 记录上一次悬停的行号
        prev_hover_idx = None
        hover_bg       = "#f3f3f3"
        normal_bg      = listbox.cget("background")  # 系统默认背景色

        def on_motion(event):
            nonlocal prev_hover_idx
            idx = listbox.nearest(event.y)           # 当前鼠标所在行
            # 判断光标是否真的在该行 bbox 内
            x, y, w, h = listbox.bbox(idx) or (0, 0, 0, 0)
            if not (y <= event.y <= y + h):
                idx = None
            # 如果行号变化，先恢复旧行，再高亮新行
            if idx != prev_hover_idx:
                if prev_hover_idx is not None:
                    listbox.itemconfig(prev_hover_idx, background=normal_bg)
                if idx is not None:
                    listbox.itemconfig(idx, background=hover_bg)
                prev_hover_idx = idx

        def on_leave(event):
            nonlocal prev_hover_idx
            if prev_hover_idx is not None:
                listbox.itemconfig(prev_hover_idx, background=normal_bg)
                prev_hover_idx = None

        listbox.bind("<Motion>", on_motion)
        listbox.bind("<Leave>",  on_leave)

        # 创建右键菜单
        context_menu = tk.Menu(dialog, tearoff=0)
        context_menu.add_command(label="删除配置", command=lambda: self.delete_config(dialog, listbox, working_dir))
        context_menu.add_command(label="重命名", command=lambda: self.edit_config_name(dialog, listbox, working_dir))

        # “打开文件位置”命令
        def open_file_location():
            sel = listbox.curselection()
            if sel:
                selected_index = sel[0]
                # 这里直接用 original_config_files，因为 listbox 中项与原列表保持同索引
                selected_file = self.original_config_files[selected_index]
                file_path = os.path.join(working_dir, selected_file)
                subprocess.Popen(f'explorer /select,"{file_path}"', creationflags=subprocess.CREATE_NO_WINDOW)

        context_menu.add_command(label="打开文件位置", command=open_file_location)

        # 辅助函数：判断事件坐标是否在某个 item 的 bbox 内
        def index_at_event(event):
            """
            返回点击位置对应的 index，如果点击在列表项的 bbox 范围内则返回对应 index，否则返回 None。
            """
            # 最近的 index
            idx = listbox.nearest(event.y)
            # 获取该 index 的 bbox；如果在可见范围内且 bbox 不为 None
            bbox = listbox.bbox(idx)
            if bbox:
                x, y, width, height = bbox  # bbox 返回 (x, y, width, height)，其中 y 是相对于 listbox 顶部的纵坐标
                if y <= event.y <= y + height:
                    return idx
            return None

        # 左键点击：如果点击空白区域，不选中任何项；如果点击在某项上，则让默认行为生效即可。
        def on_left_click(event):
            idx = index_at_event(event)
            if idx is None:
                # 点击空白区域：清除选中，阻止默认可能选中“nearest”的行为
                listbox.selection_clear(0, tk.END)
                # 返回 "break" 可以阻止后续默认事件处理，避免选中 nearest 项
                return "break"
            # 点击在某一项上，让默认行为（选中等）继续执行
            # 不返回 "break" 即可

        # 右键点击：只有点击在某项上时才显示菜单，并选中该项；点击空白区域时，不显示菜单
        def on_right_click(event):
            idx = index_at_event(event)
            if idx is not None:
                # 在项上点击：先选中该项（更新 selection），再弹出菜单
                listbox.selection_clear(0, tk.END)
                listbox.selection_set(idx)
                listbox.activate(idx)
                context_menu.post(event.x_root, event.y_root)
            else:
                # 点击空白区域，不做任何事，也不弹菜单
                return "break"

        # 绑定左键和右键
        listbox.bind("<Button-1>", on_left_click)
        # Windows 下通常 <Button-3> 是右键；在 macOS 可能用 <Button-2>，此处按照 Windows 右键绑定。
        listbox.bind("<Button-3>", on_right_click)

        # 按钮框架 - 放在列表框下方
        button_frame = tk.Frame(main_frame)
        button_frame.pack(pady=(10, 0))
        # 按钮定义
        def on_ok():
            selection = listbox.curselection()
            if not selection:
                messagebox.showwarning("警告", "请选择一个配置文件", parent=dialog)
                return
            global selected_config
            # 获取原始文件名（去掉可能添加的后缀）
            selected_display = listbox.get(selection[0])
            selected_config = selected_display.split(" (当前配置)")[0]
            dialog.destroy()

        def on_cancel():
            global selected_config
            selected_config = None
            dialog.destroy()

        # 在创建按钮时添加bootstyle参数
        save_button = ttk.Button(
            button_frame, 
            text="加载", 
            command=on_ok,
            bootstyle="primary-outline"  
        )
        save_button.pack(side=tk.RIGHT, padx=5)

        cancel_button = ttk.Button(
            button_frame, 
            text="取消", 
            command=on_cancel,
            bootstyle="primary-outline"  
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)
        
        # 让 Tkinter 计算“理想”大小
        dialog.update_idletasks()
        req_w = dialog.winfo_reqwidth()
        req_h = dialog.winfo_reqheight()

        # 目标比例
        ratio_w, ratio_h = 4 , 5

        # 方案 A：以理想宽度 req_w 为基准，计算对应的高度
        h_based_on_w = int(req_w * ratio_h / ratio_w)
        # 方案 B：以理想高度 req_h 为基准，计算对应的宽度
        w_based_on_h = int(req_h * ratio_w / ratio_h)

        # 选择能包下所有控件的最小方案
        # 如果 h_based_on_w >= req_h，就用 (req_w, h_based_on_w)，否则用 (w_based_on_h, req_h)
        if h_based_on_w >= req_h:
            new_w, new_h = req_w, h_based_on_w
        else:
            new_w, new_h = w_based_on_h, req_h

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - new_w) // 2
        y = main_y + (main_h - new_h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{new_w}x{new_h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")
        
        dialog.protocol("WM_DELETE_WINDOW", on_cancel)
        self.root.wait_window(dialog)
        self.load_selected_config()

    def load_selected_config(self):
        step_count = 0
        global selected_config
        try:  
            if self.import_and_load:
                selected_config = self.import_config_filename
            if not selected_config and not self.import_and_load:
                return False
            # 保存最后使用的配置
            self.save_last_used_config(selected_config)
            # 获取程序工作目录
            working_dir = os.getcwd()
            # 加载配置文件
            self.config_filename = os.path.join(working_dir, selected_config)

            if not os.path.exists(self.config_filename):
                raise FileNotFoundError(f"配置文件不存在: {self.config_filename}")

            # 先读取配置文件
            with open(self.config_filename, 'r', encoding='utf-8') as f:
                config = json.load(f)           

            # 在应用任何更改之前，先验证所有图像文件
            missing_images = []
            existing_image_paths = set()

            config_basename = Path(self.config_filename).stem  # 不带扩展名
            config_folder_dir = Path(self.screenshot_folder) / config_basename

            # 收集存在的图片路径
            for img_data in config.get('image_list', []):
                image_path = Path(img_data[0])
                if image_path.exists():
                    existing_image_paths.add(image_path.resolve())  # 保存绝对路径
                else:
                    missing_images.append(str(image_path))

            # 删除 config_folder_dir 中未在 image_list 中的文件
            for file in config_folder_dir.iterdir():
                if file.is_file() and file.resolve() not in existing_image_paths:
                    file.unlink()
                    print (f"已删除配置中不存在的图片: {file}")
                    logging.info (f"已删除配置中不存在的图片: {file}")

            # 如果有任何图像文件不存在，直接返回，不做任何更改
            if missing_images:
                error_message = f"配置文件中缺少以下图像文件: {', '.join(missing_images)}"
                messagebox.showerror("错误", error_message, parent=self.root)
                logging.error(error_message)
                return False                  

            # 只有当所有图像文件都存在时，才应用配置
            self.image_list = config.get('image_list', [])
            self.hotkey = config.get('hotkey', '<F9>')
            self.similarity_threshold = config.get('similarity_threshold', 0.8)
            self.delay_time = config.get('delay_time', 0.1)
            self.loop_count = config.get('loop_count', 1)
            self.only_keyboard_var.set(config.get('only_keyboard', False))

            # 清空并重新填充 Treeview
            for item in self.tree.get_children():
                self.tree.delete(item)
                
            for i, img_data in enumerate(self.image_list):
                # 确保每个项目都有全部索引的数量
                if len(img_data) < 15: #新增索引
                    img_data += [""] * (15 - len(img_data))
                    self.image_list[i] = img_data  # 更新原列表中的内容

                # 处理识图区域（img_data[14]）
                if not img_data[14]:  # 如果为空
                    # 1. 读取屏幕分辨率备用
                    screen_w = self.root.winfo_screenwidth()
                    screen_h = self.root.winfo_screenheight()

                    # 2. 尝试从 img_data[0] 路径读取图片分辨率
                    img_path = img_data[0]
                    img_w, img_h = None, None
                    try:
                        # 如果路径可能相对，你可以根据需要调整基路径
                        if not os.path.isabs(img_path):
                            # 假设 img_path 相对于当前工作目录，或改为 project 根目录等
                            img_path = os.path.abspath(img_path)
                        with Image.open(img_path) as img:
                            img_w, img_h = img.size  # 宽度、高度
                    except Exception as e:
                        # 读取失败时，使用全屏作为 fallback（或其它默认值）
                        img_w, img_h = screen_w, screen_h

                    # 3. 从 img_data[4] 解析中心点坐标，示例 "click:817,955:0:1"
                    center_x = center_y = None
                    coord_str = img_data[4]  # 例如 "815,958" 或 "click:817,955:0:1"
                    if ':' in coord_str:
                        parts = coord_str.split(':')
                        # 期望 parts[1] 是 "817,955"
                        if len(parts) > 1 and ',' in parts[1]:
                            coord_part = parts[1]
                        else:
                            coord_part = coord_str
                    else:
                        # 没有冒号，直接当成 "x,y"
                        coord_part = coord_str

                    # 解析 coord_part
                    try:
                        cx_str, cy_str = coord_part.split(',')
                        center_x = int(cx_str)
                        center_y = int(cy_str)
                    except Exception as e:
                        center_x = screen_w // 2
                        center_y = screen_h // 2

                    # 4. 计算包围区域：以图片宽高为尺寸，中心点裁出矩形
                    offset = 20

                    half_w = img_w // 2
                    half_h = img_h // 2
                    left = center_x - half_w - offset
                    top = center_y - half_h - offset 
                    right = center_x + half_w + offset
                    bottom = center_y + half_h + offset

                    # 可选：确保不超过屏幕边界
                    left = max(0, left)
                    top = max(0, top)
                    right = min(screen_w, right)
                    bottom = min(screen_h, bottom)

                    img_coords = f"{left},{top},{right},{bottom}" 
                    img_data[14] = f"0,0,{screen_w},{screen_h}|update|{img_coords}"
                    self.image_list[i] = img_data  # 更新列表
                    if step_count == 0:
                        messagebox.showinfo("提示", f"检测到旧版本配置文件\n首次运行步骤将更新识图区域，此时运行速度较慢\n所有步骤更新完识图区域后，运行速度将大幅提升！")

                # 加载图像并创建缩略图
                try:
                    image = Image.open(img_data[0])
                    image.thumbnail((50, 50))
                    photo = ImageTk.PhotoImage(image)

                    # 插入到 Treeview
                    tree_item = self.tree.insert(
                        "", 
                        tk.END,
                        values=(
                            os.path.basename(img_data[0]),  # 特殊处理的图片名
                            *img_data[1:]  # 自动包含所有配置字段
                        ),
                        image=photo
                    )
                    self.tree.image_refs.append(photo)
                    step_count += 1
                except Exception as e:
                    print(f"处理图像时出错 {img_data[0]}: {e}")
                    logging.error(f"处理图像时出错 {img_data[0]}: {e}")
      
            # 更新循环次数输入框
            self.loop_count_entry.delete(0, tk.END)
            self.loop_count_entry.insert(0, str(self.loop_count))
            self.config_loaded = True
            
            # 取消之前的全局热键， 注册新的全局热键
            self.unregister_global_hotkey()
            self.register_global_hotkey()
            self.update_image_listbox()
            
            print(f"已从 {self.config_filename} 加载{step_count}个步骤")
            logging.info(f"已从 {self.config_filename} 加载{step_count}个步骤")
            
            # 显示成功消息
            # messagebox.showinfo("成功", f"配置已成功加载:\n{self.config_filename}", parent=self.root)
            self.import_and_load = False
            return True
            
        except Exception as e:
            error_message = f"加载配置时出错: {str(e)}"
            print(error_message)
            logging.error(error_message)
            messagebox.showerror("错误", error_message, parent=self.root)
            return False
        
    def export_config(self):
        try:
            # 获取程序工作目录
            working_dir = os.getcwd()
            
            # 查找根目录下的所有 .json 配置文件
            config_files = [f for f in os.listdir(working_dir) if f.endswith('.json') and f != 'last_config.json']
            if not config_files:
                messagebox.showinfo("提示", "没有找到任何配置文件", parent=self.root)
                return

            # 创建一个 Toplevel 窗口
            export_window = tk.Toplevel(self.root)
            export_window.withdraw()                     # 先隐藏
            export_window.title("选择配置文件导出")
            export_window.transient(self.root)
            export_window.grab_set()

            # 主容器框架
            main_frame = tk.Frame(export_window)
            main_frame.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)

            # 搜索框区域
            style = tb.Style()  
            style.configure("Border.TFrame", background="#ced4da")
            style.configure("InnerR.TFrame", background="white")
            border_width = 1

            # 外层 Frame 模拟边框
            search_border = tb.Frame(main_frame)
            search_border.pack(fill=tk.X, expand=True, padx=0, pady=5)
            search_border.configure(style="Border.TFrame")

            # 内层 Frame 白底（必须使用 bootstyle="light"）
            search_inner = tb.Frame(
                search_border, 
                bootstyle="light",
                style="InnerR.TFrame"
            )
            search_inner.pack(fill=tk.X, expand=True, padx=border_width, pady=border_width)

            search_var = tk.StringVar()
            # 定义所有状态下的边框颜色为白色
            style.map(
                'White.TEntry',
                bordercolor=[
                    ('active', 'white'),    # 鼠标悬停/激活状态
                    ('focus', 'white'),     # 获取焦点状态
                    ('disabled', 'white'),  # 禁用状态
                    ('!disabled', 'white')  # 默认状态
                ],
                lightcolor=[('', 'white')],  # 未选中时的边框高亮
                darkcolor=[('', 'white')]    # 阴影颜色
            )
            # 配置基础样式
            style.configure(
                'White.TEntry',
                foreground='black',          # 文字颜色
                fieldbackground='white',     # 背景色
                borderwidth=1               # 边框宽度
            )
            # 创建并应用 Entry
            search_var = tk.StringVar()
            entry = Entry(
                search_inner,
                textvariable=search_var,
                style='White.TEntry',
            )
            entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 0), pady=0)

            # 图标
            img = Image.open("icon/search.png").resize((16, 16), Image.Resampling.LANCZOS)
            search_icon = ImageTk.PhotoImage(img)

            icon_label = tk.Label(search_inner, image=search_icon, bg="white", bd=0)
            icon_label.image = search_icon  # 防止被垃圾回收
            icon_label.pack(side=tk.RIGHT, padx=5)

            placeholder_original = "在导出配置中搜索"
            placeholder = f"{placeholder_original}"  # 统一使用这个变量

            def set_placeholder():
                entry.delete(0, tk.END)
                entry.insert(0, placeholder)
                entry.config(foreground='grey')

            def clear_placeholder(event=None):
                if entry.get() == placeholder:
                    entry.delete(0, tk.END)
                    entry.config(foreground='black')

            def restore_placeholder(event=None):
                if not entry.get():
                    set_placeholder()
                    
            def on_search(*args):
                text = search_var.get().strip()
                if text == "" or text == placeholder_original:
                    update_listbox("")  # 显示所有
                else:
                    update_listbox(text)

            # 初始化 placeholder
            set_placeholder()

            # 事件绑定
            entry.bind("<FocusIn>", clear_placeholder)
            entry.bind("<FocusOut>", restore_placeholder)
            search_var.trace_add('write', on_search)

            # 列表框容器
            list_container = tk.Frame(main_frame)
            list_container.pack(fill=tk.BOTH, expand=True)

            # 列表框和滚动条
            listbox = tk.Listbox(list_container, selectmode=tk.SINGLE)
            scrollbar = tk.Scrollbar(list_container)

            scrollbar.config(command=listbox.yview)
            listbox.config(yscrollcommand=scrollbar.set)

            current_loaded = os.path.basename(self.config_filename) if hasattr(self, 'config_filename') and self.config_filename else None

            # 保存原始文件列表
            self.original_config_files = config_files

            def update_listbox(filter_text=""):
                listbox.delete(0, tk.END)
                for config_file in self.original_config_files:
                    if filter_text.lower() in config_file.lower():
                        display_name = config_file
                        if current_loaded and config_file == current_loaded:
                            display_name = f"{config_file} (当前配置)"
                        listbox.insert(tk.END, display_name)
                        
            update_listbox()
            # 绑定双击事件
            # 先定义一个判断点击是否在 item 上的函数（可复用之前的 index_at_event）
            def index_at_event(event):
                idx = listbox.nearest(event.y)
                bbox = listbox.bbox(idx)
                if bbox:
                    x, y, w, h = bbox
                    if y <= event.y <= y + h:
                        return idx
                return None

            # 双击回调：先判断是否点在有效行上，再调用 edit_config_name
            def on_double_click(event):
                idx = index_at_event(event)
                if idx is None:
                    return  # 点击空白，直接返回
                # 选中该行（可选，edit_config_name 内部也会检查 selection）
                listbox.selection_clear(0, tk.END)
                listbox.selection_set(idx)
                listbox.activate(idx)
                # 这里正确传递 export_window，而不是 event
                self.edit_config_name(export_window, listbox, working_dir, event)

            # 绑定时，不要把 event 误传为 export_window
            listbox.bind("<Double-Button-1>", on_double_click)

            # 使用grid布局让列表框和滚动条并排
            listbox.grid(row=0, column=0, sticky="nsew")
            scrollbar.grid(row=0, column=1, sticky="ns")

            # 配置grid权重
            list_container.grid_rowconfigure(0, weight=1)
            list_container.grid_columnconfigure(0, weight=1)

            # 记录上一次悬停的行号
            prev_hover_idx = None
            hover_bg       = "#f3f3f3"
            normal_bg      = listbox.cget("background")  # 系统默认背景色

            def on_motion(event):
                nonlocal prev_hover_idx
                idx = listbox.nearest(event.y)           # 当前鼠标所在行
                # 判断光标是否真的在该行 bbox 内
                x, y, w, h = listbox.bbox(idx) or (0, 0, 0, 0)
                if not (y <= event.y <= y + h):
                    idx = None
                # 如果行号变化，先恢复旧行，再高亮新行
                if idx != prev_hover_idx:
                    if prev_hover_idx is not None:
                        listbox.itemconfig(prev_hover_idx, background=normal_bg)
                    if idx is not None:
                        listbox.itemconfig(idx, background=hover_bg)
                    prev_hover_idx = idx

            def on_leave(event):
                nonlocal prev_hover_idx
                if prev_hover_idx is not None:
                    listbox.itemconfig(prev_hover_idx, background=normal_bg)
                    prev_hover_idx = None

            listbox.bind("<Motion>", on_motion)
            listbox.bind("<Leave>",  on_leave)

            # 创建右键菜单
            context_menu = tk.Menu(export_window, tearoff=0)
            context_menu.add_command(label="删除配置", command=lambda: self.delete_config(export_window, listbox, working_dir))
            context_menu.add_command(label="重命名", command=lambda: self.edit_config_name(export_window, listbox, working_dir))

            # “打开文件位置”命令
            def open_file_location():
                sel = listbox.curselection()
                if sel:
                    selected_index = sel[0]
                    # 这里直接用 original_config_files，因为 listbox 中项与原列表保持同索引
                    selected_file = self.original_config_files[selected_index]
                    file_path = os.path.join(working_dir, selected_file)
                    subprocess.Popen(f'explorer /select,"{file_path}"', creationflags=subprocess.CREATE_NO_WINDOW)

            context_menu.add_command(label="打开文件位置", command=open_file_location)

            # 辅助函数：判断事件坐标是否在某个 item 的 bbox 内
            def index_at_event(event):
                """
                返回点击位置对应的 index，如果点击在列表项的 bbox 范围内则返回对应 index，否则返回 None。
                """
                # 最近的 index
                idx = listbox.nearest(event.y)
                # 获取该 index 的 bbox；如果在可见范围内且 bbox 不为 None
                bbox = listbox.bbox(idx)
                if bbox:
                    x, y, width, height = bbox  # bbox 返回 (x, y, width, height)，其中 y 是相对于 listbox 顶部的纵坐标
                    if y <= event.y <= y + height:
                        return idx
                return None

            # 左键点击：如果点击空白区域，不选中任何项；如果点击在某项上，则让默认行为生效即可。
            def on_left_click(event):
                idx = index_at_event(event)
                if idx is None:
                    # 点击空白区域：清除选中，阻止默认可能选中“nearest”的行为
                    listbox.selection_clear(0, tk.END)
                    # 返回 "break" 可以阻止后续默认事件处理，避免选中 nearest 项
                    return "break"
                # 点击在某一项上，让默认行为（选中等）继续执行
                # 不返回 "break" 即可

            # 右键点击：只有点击在某项上时才显示菜单，并选中该项；点击空白区域时，不显示菜单
            def on_right_click(event):
                idx = index_at_event(event)
                if idx is not None:
                    # 在项上点击：先选中该项（更新 selection），再弹出菜单
                    listbox.selection_clear(0, tk.END)
                    listbox.selection_set(idx)
                    listbox.activate(idx)
                    context_menu.post(event.x_root, event.y_root)
                else:
                    # 点击空白区域，不做任何事，也不弹菜单
                    return "break"

            # 绑定左键和右键
            listbox.bind("<Button-1>", on_left_click)
            # Windows 下通常 <Button-3> 是右键；在 macOS 可能用 <Button-2>，此处按照 Windows 右键绑定。
            listbox.bind("<Button-3>", on_right_click)

            # 按钮框架 - 放在列表框下方
            button_frame = tk.Frame(main_frame)
            button_frame.pack(pady=(10, 0))

            def confirm_export():
                try:
                    selection = listbox.curselection()
                    if not selection:
                        messagebox.showwarning("警告", "请先选择一个配置文件！", parent=export_window)
                        return
                    
                    selected_file = config_files[selection[0]]
                    config_basename = os.path.splitext(selected_file)[0]
                    config_path = os.path.join(working_dir, selected_file)
                    image_folder = os.path.join(working_dir, "screenshots", config_basename)

                    # 让用户选择 ZIP 文件的保存位置
                    export_zip_path = filedialog.asksaveasfilename(
                        title="保存为 ZIP 文件",
                        defaultextension=".zip",
                        initialfile=config_basename,
                        filetypes=[("ZIP 压缩文件", "*.zip")],
                        parent=export_window
                    )
                    
                    if not export_zip_path:
                        return

                    # 创建 ZIP 文件
                    try:
                        with zipfile.ZipFile(export_zip_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
                            zipf.write(config_path, os.path.basename(config_path))
                            
                            if os.path.exists(image_folder):
                                for root, _, files in os.walk(image_folder):
                                    for file in files:
                                        file_path = os.path.join(root, file)
                                        zip_path = os.path.join("screenshots", config_basename, os.path.relpath(file_path, image_folder))
                                        zipf.write(file_path, zip_path)
                        
                        messagebox.showinfo(
                            "导出成功",
                            f"配置文件和图片已打包成 ZIP 文件：\n{export_zip_path}",
                            parent=export_window
                        )
                        export_window.destroy()
                    except Exception as e:
                        messagebox.showerror("错误", f"ZIP 打包失败：{str(e)}", parent=export_window)
                except Exception as e:
                    logging.error(f"导出过程中出错: {str(e)}")
                    messagebox.showerror("错误", f"导出过程中出错: {str(e)}", parent=export_window)

            # 在创建按钮时添加bootstyle参数
            save_button = ttk.Button(
                button_frame, 
                text="导出", 
                command=confirm_export,
                bootstyle="primary-outline"  
            )
            save_button.pack(side=tk.RIGHT, padx=5)

            cancel_button = ttk.Button(
                button_frame, 
                text="取消", 
                command=export_window.destroy,
                bootstyle="primary-outline"  
            )
            cancel_button.pack(side=tk.RIGHT, padx=5)
            export_window.iconbitmap("icon/app.ico")  # 设置窗口图标

            # 让 Tkinter 计算“理想”大小
            export_window.update_idletasks()
            req_w = export_window.winfo_reqwidth()
            req_h = export_window.winfo_reqheight()

            # 目标比例
            ratio_w, ratio_h = 4 , 5

            # 方案 A：以理想宽度 req_w 为基准，计算对应的高度
            h_based_on_w = int(req_w * ratio_h / ratio_w)
            # 方案 B：以理想高度 req_h 为基准，计算对应的宽度
            w_based_on_h = int(req_h * ratio_w / ratio_h)

            # 选择能包下所有控件的最小方案
            # 如果 h_based_on_w >= req_h，就用 (req_w, h_based_on_w)，否则用 (w_based_on_h, req_h)
            if h_based_on_w >= req_h:
                new_w, new_h = req_w, h_based_on_w
            else:
                new_w, new_h = w_based_on_h, req_h

            # 计算居中位置
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_w = self.root.winfo_width()
            main_h = self.root.winfo_height()
            x = main_x + (main_w - new_w) // 2
            y = main_y + (main_h - new_h) // 2

            # 一次性设置大小和位置，并显示
            export_window.geometry(f"{new_w}x{new_h}+{x}+{y}")
            export_window.deiconify()

        except Exception as e:
            logging.error(f"导出配置时出错: {str(e)}")
            messagebox.showerror("导出失败", f"导出配置时出错: {str(e)}", parent=self.root)

    def import_config(self):
        try:
            # 弹出文件选择对话框，支持选择.json或.zip文件
            filename = filedialog.askopenfilename(
                filetypes=[
                    ("JSON/ZIP files", "*.json;*.zip"),
                    ("JSON files", "*.json"),
                    ("ZIP files", "*.zip")
                ]
            )
            if not filename:
                return
            
            screenshots_dir = self.screenshot_folder
            if not os.path.exists(screenshots_dir):
                os.makedirs(screenshots_dir)

            # 处理ZIP文件导入
            if filename.endswith('.zip'):
                with zipfile.ZipFile(filename, 'r') as zip_ref:
                    # 提取所有文件到临时目录
                    temp_dir = tempfile.mkdtemp()
                    zip_ref.extractall(temp_dir)
                    
                    # 查找解压后的.json配置文件
                    json_files = [f for f in os.listdir(temp_dir) if f.endswith('.json')]
                    if not json_files:
                        messagebox.showerror("错误", "ZIP文件中未找到配置文件")
                        shutil.rmtree(temp_dir)
                        return
                    
                    # 只处理第一个找到的.json文件
                    config_file = json_files[0]
                    config_basename = os.path.splitext(config_file)[0]
                    self.import_config_filename = os.path.basename(config_file)
                    
                    # 导入配置文件
                    src_config = os.path.join(temp_dir, config_file)
                    dst_config = os.path.join(config_file)
                    shutil.copy2(src_config, dst_config)
                    
                    # 导入图片文件夹（如果存在）
                    src_images = os.path.join(temp_dir, "screenshots", config_basename)
                    if os.path.exists(src_images):
                        dst_images = os.path.join(screenshots_dir, config_basename)
                        if os.path.exists(dst_images):
                            shutil.rmtree(dst_images)
                        shutil.copytree(src_images, dst_images)
                    
                    shutil.rmtree(temp_dir)
                    self.import_and_load = True
                    self.load_selected_config() 
                    messagebox.showinfo("导入成功", f"配置文件及关联图片已成功导入！")
            
            # 处理JSON文件导入
            elif filename.endswith('.json'):
                config_basename = os.path.splitext(os.path.basename(filename))[0]
                self.import_config_filename = os.path.basename(filename)
                
                # 导入配置文件
                new_config_path = os.path.join(screenshots_dir, os.path.basename(filename))
                shutil.copy2(filename, new_config_path)
                
                # 尝试导入同级目录下的图片文件夹
                image_folder = os.path.join(os.path.dirname(filename), config_basename)
                if os.path.exists(image_folder):
                    new_image_folder = os.path.join(screenshots_dir, config_basename)
                    if os.path.exists(new_image_folder):
                        shutil.rmtree(new_image_folder)
                    shutil.copytree(image_folder, new_image_folder)
                self.import_and_load = True
                self.load_selected_config()   
                messagebox.showinfo("导入成功", f"配置文件及关联图片已成功导入！")
                
        except Exception as e:
            logging.error(f"导入配置时出错: {str(e)}")
            messagebox.showerror("导入失败", f"导入配置时出错: {str(e)}")

    def edit_config_name(self, dialog, listbox, working_dir, event=None):
        selection = listbox.curselection()
        if not selection:
            messagebox.showwarning("警告", "请先选择一个配置文件", parent=dialog)
            return

        idx = selection[0]
        config_item = listbox.get(idx).replace("(当前配置)", "").strip()
        config_path = os.path.join(working_dir, config_item)

        old_name, ext = os.path.splitext(config_item)
        folder_path = os.path.join(self.screenshot_folder, old_name)

        bbox = listbox.bbox(idx)
        if not bbox:
            return

        x, y, width, height = bbox
        current_value = old_name

        # 如果已有正在编辑的 entry，先销毁它
        if hasattr(self, 'rename_entry') and self.rename_entry:
            try:
                self.rename_entry.destroy()
            except:
                pass
            self.rename_entry = None

        entry = tk.Entry(listbox)
        entry.place(x=x, y=y, width=width, height=height)
        entry.insert(0, current_value)
        entry.select_range(0, tk.END)
        entry.focus()
        # 保存当前编辑信息，以便在其他点击时能提交
        self.rename_entry = entry
        self.rename_entry_index = idx
        self.rename_old_name = old_name
        self.rename_ext = ext
        self.rename_dialog = dialog
        self.rename_working_dir = working_dir

        def on_save(event=None):
            # 如果 entry 已被销毁或不是当前 entry，跳过
            if not hasattr(self, 'rename_entry') or self.rename_entry is None:
                return
            new_name = entry.get().strip()
            # 先销毁 entry，避免重复
            entry.destroy()
            self.rename_entry = None

            if not new_name or new_name == old_name:
                return

            new_config_file = new_name + ext
            new_config_path = os.path.join(working_dir, new_config_file)
            new_folder_path = os.path.join(self.screenshot_folder, new_name)

            should_reload_config = False
            if config_path == self.config_filename:
                should_reload_config = True

            if os.path.exists(new_config_path):
                messagebox.showerror("错误", f"配置文件“{new_config_file}”已存在！", parent=dialog)
                return

            try:
                os.rename(config_path, new_config_path)
                if os.path.exists(folder_path):
                    if not os.path.exists(new_folder_path):
                        os.rename(folder_path, new_folder_path)
                # 更新配置内容中 paths
                with open(new_config_path, 'r', encoding='utf-8') as f:
                    config_data = json.load(f)
                if 'image_list' in config_data:
                    for img_data in config_data['image_list']:
                        path = Path(img_data[0])
                        if len(path.parts) >= 3 and path.parts[0] == 'screenshots':
                            # parts[1] 是旧 config 名称，改为 new_name
                            new_path = Path(path.parts[0]) / new_name / Path(*path.parts[2:])
                            img_data[0] = str(new_path)
                    with open(new_config_path, 'w', encoding='utf-8') as f:
                        json.dump(config_data, f, ensure_ascii=False, indent=2)
                else:
                    pass

                # 更新列表和原始列表
                self.original_config_files[idx] = new_config_file
                listbox.delete(idx)
                display_name = new_config_file

                listbox.insert(idx, display_name)
                listbox.selection_set(idx)

                if should_reload_config:
                    self.clear_list()

            except Exception as e:
                messagebox.showerror("重命名失败", str(e), parent=dialog)

        # 绑定回车保存
        entry.bind('<Return>', on_save)
        # 绑定焦点丢失保存
        entry.bind('<FocusOut>', on_save)

        # 为了在点击列表其他地方时先提交编辑，给 listbox 绑定一个点击事件
        def commit_rename_on_click(event):
            # 如果当前有正在编辑的 entry，则先保存它
            if hasattr(self, 'rename_entry') and self.rename_entry:
                on_save()
                
        listbox.unbind('<Button-1>', None)
        listbox.bind('<Button-1>', commit_rename_on_click, add='+')

    def delete_config(self, dialog, listbox, working_dir):
        """删除选中的配置文件及其关联文件夹"""
        selection = listbox.curselection()
        if not selection:
            messagebox.showwarning("警告", "请先选择一个配置文件", parent=dialog)
            return
        config_file = listbox.get(selection[0]).replace("(当前配置)", "").strip()
        last_config_record = self.last_used_config
        config_path = os.path.join(working_dir, config_file)
        # 获取关联文件夹名称
        folder_name = os.path.splitext(config_file)[0]
        folder_path = os.path.join(self.screenshot_folder, folder_name)

        if config_path == self.config_filename:    
            # 确认删除
            confirm = messagebox.askokcancel("警告", 
                                        f"正在加载当前配置，确认删除后，加载的配置将丢失！\n【以下内容将被删除】\n配置文件: {config_file}\n关联文件夹: {folder_name}",
                                        icon="warning",  # 添加警告图标
                                        parent=dialog)  
        else:
            # 确认删除
            confirm = messagebox.askyesno("确认删除", 
                                        f"确定要删除以下内容吗？\n配置文件: {config_file}\n关联文件夹: {folder_name}",
                                        parent=dialog)
        if not confirm:
            return    
        try:
            if config_path == self.config_filename:
                self.clear_list()
            # 删除配置文件
            if os.path.exists(config_path):
                os.remove(config_path)       
            # 删除关联文件夹（如果存在）
            if os.path.exists(folder_path) and os.path.isdir(folder_path):
                shutil.rmtree(folder_path)  
            # 清空上一次加载的配置文件记录
            if os.path.exists(last_config_record):
                os.remove(last_config_record)       
            # 从列表框中移除
            listbox.delete(selection[0])        
        except Exception as e:
            messagebox.showerror("错误", f"删除时出错: {str(e)}", parent=dialog)
            logging.error(f"删除配置文件时出错: {str(e)}")

    def reset_to_initial_state(self):
        """重置程序到初始状态"""
        try:
            # 重置所有变量到初始值
            self.hotkey = '<F9>'
            self.similarity_threshold = 0.8
            self.delay_time = 0.1
            self.loop_count = 1
            self.image_list = []
            self.running = False
            self.paused = False
            self.start_step_index = 0
            self.only_keyboard_var.set(False)
            self.config_filename = None  

            # 清空上一次加载的配置文件记录
            if os.path.exists(self.last_used_config):
                os.remove(self.last_used_config)    
               
            # 重置界面元素
            self.update_image_listbox()
            self.loop_count_entry.delete(0, tk.END)
            self.loop_count_entry.insert(0, str(self.loop_count))
            self.toggle_run_button.config(text="开始运行(F9)")
               
            print("程序已重置为初始状态")
            logging.info("程序已重置为初始状态")      
            #  取消之前的全局热键， 注册新的全局热键
            self.unregister_global_hotkey()
            self.register_global_hotkey()
        except Exception as e:
            print(f"重置程序状态时出错: {e}")
            logging.error(f"重置程序状态时出错: {e}")
   
    def get_mouse_position(self, event=None):
        # 获取当前鼠标位置
        x, y = pyautogui.position()
    
        # 将鼠标位置存储到当前选中的图像中
        selected_item = self.tree.selection()
        if selected_item:
            selected_index = self.tree.index(selected_item[0])
            selected_image = self.image_list[selected_index]
            
            # 保留原有的鼠标动作设置，只更新坐标部分
            if selected_image[4] and ":" in selected_image[4]:  # 如果有现有的鼠标动作数据
                parts = selected_image[4].split(":")
                action = parts[0]
                dynamic = parts[2] if len(parts) > 2 else "0"
                count = parts[3] if len(parts) > 3 else "1"
                # 重新构建鼠标动作字符串
                mouse_action = f"{action}:{x},{y}:{dynamic}"
                if action in ["click", "scrollUp", "scrollDown"]:
                    mouse_action += f":{count}"
            else:
                # 如果没有鼠标动作数据，使用默认的单击动作
                mouse_action = f"click:{x},{y}:0:1"
            
            tpl = tuple(selected_image)
            # 修改索引 4：
            new_image = tpl[:4] + (mouse_action,) + tpl[5:]
            self.image_list[selected_index] = new_image

            step_name = selected_image[1]
            old_coodr = selected_image[4].split(":")[1] if selected_image[4] and ":" in selected_image[4] else selected_image[4]
            new_coodr = x, y
            logging.info(f"【{step_name}】坐标更新：({old_coodr}) → {new_coodr}")      
            print(f"【{step_name}】坐标更新：({old_coodr}) → {new_coodr}")
            
            self.update_image_listbox()
            messagebox.showinfo("更新坐标", f"坐标已更新为({x}, {y})")

        else:
            messagebox.showerror("错误", "请选中1个步骤后重试")
            return
   
    def cleanup_on_exit(self):
        try:
            # 退出程序时删除未保存的图像
            screenshots_dir = self.screenshot_folder
            if os.path.exists(screenshots_dir):
                # 获取screenshots文件夹中所有文件（不包括子目录）
                files_to_delete = [f for f in os.listdir(screenshots_dir) 
                                if os.path.isfile(os.path.join(screenshots_dir, f))]
                
                for filename in files_to_delete:
                    img_path = os.path.join(screenshots_dir, filename)
                    try:
                        os.remove(img_path)
                        print(f"图像文件已删除: {img_path}")
                        logging.info(f"图像文件已删除: {img_path}")
                    except Exception as e:
                        print(f"删除图像文件时出错: {e}")
                        logging.error(f"删除图像文件时出错: {e}")
            
            # 取消全局热键
            self.unregister_global_hotkey()
        except Exception as e:
            print(f"清理时出错: {e}")
            logging.error(f"清理时出错: {e}")
   
    def bind_arrow_keys(self):
        self.tree.bind('<Up>', self.move_item_up)
        self.tree.bind('<Down>', self.move_item_down)
   
    def move_item_up(self, event):
        selected_items = self.tree.selection()
        if not selected_items:
            return
   
        for item in selected_items:
            index = self.tree.index(item)
            if index > 0:
                self.tree.move(item, '', index - 1)
                self.image_list.insert(index - 1, self.image_list.pop(index))
   
        # 确保第一个选定项目可见
        self.tree.see(selected_items[0])
   
        # 阻止事件传播
        return "break"
   
    def move_item_down(self, event):
        selected_items = self.tree.selection()
        if not selected_items:
            return
   
        for item in reversed(selected_items):
            index = self.tree.index(item)
            if index < len(self.image_list) - 1:
                self.tree.move(item, '', index + 1)
                self.image_list.insert(index + 1, self.image_list.pop(index))
   
        # 确保最后一项可见
        self.tree.see(selected_items[-1])
   
        # 阻止事件传播
        return "break"
   
    def create_context_menu(self):
        # 空白处的菜单
        self.empty_space_menu = tk.Menu(self.root, tearoff=0)
        self.empty_space_menu.add_command(label="清空列表", command=self.clear_list)
        self.empty_space_menu.add_separator()
        self.empty_space_menu.add_command(label="粘贴", command=self.paste_item)
        self.empty_space_menu.add_separator()
        self.empty_space_menu.add_command(label="保存配置", command=self.save_config)
        self.empty_space_menu.add_command(label="加载配置", command=self.load_config)
        self.empty_space_menu.add_separator()
        self.empty_space_menu.add_command(label="查看日志", command=self.show_logs)
        self.empty_space_menu.add_command(label="检查更新", command=self.check_update)

        # 选中项的菜单
        self.context_menu = tk.Menu(self.root, tearoff=0, postcommand=self.update_context_menu)
        self.context_menu.add_command(label="重新截图(F4)", command=self.retake_screenshot)  # 菜单索引0
        self.context_menu.add_command(label="关闭识图", command=self.Image_recognition_click)  # 菜单索引1
        self.context_menu.add_command(label="识图区域", command=self.image_rc_area)
        self.context_menu.add_command(label="条件判断", command=self.set_condition_jump)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="复制", command=self.copy_item)
        self.context_menu.add_command(label="剪切", command=self.cut_item)
        self.context_menu.add_command(label="粘贴", command=self.paste_item)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="删除", command=self.delete_selected_image)
        self.context_menu.add_command(label="禁用", command=self.toggle_disable_status)  # 菜单索引10
        self.context_menu.add_separator()
        self.context_menu.add_command(label="从此步骤运行", command=self.start_from_step)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="打开图片位置", command=self.open_image_location)
        self.context_menu.add_separator()

        # 创建“更多选项”子菜单
        more_menu = tk.Menu(self.context_menu, tearoff=0)
        more_menu.add_command(label="重命名", command=self.edit_step_name)
        more_menu.add_command(label="延时ms", command=self.edit_wait_time)
        more_menu.add_command(label="相似度", command=self.edit_similarity_threshold)
        more_menu.add_command(label="键盘动作", command=self.edit_keyboard_input)
        more_menu.add_command(label="鼠标动作", command=self.edit_mouse_action)
        more_menu.add_command(label="偏移坐标", command=self.offset_coords)

        # 把子菜单添加到主菜单
        self.context_menu.add_cascade(label="更多选项", menu=more_menu)

        self.context_menu.add_separator()
        self.context_menu.add_command(label="清空列表", command=self.clear_list)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="查看日志", command=self.show_logs)
        self.context_menu.add_command(label="检查更新", command=self.check_update)

        # 多选菜单
        self.multi_select_menu = tk.Menu(self.root, tearoff=0)
        self.multi_select_menu.add_command(label="复制", command=self.copy_item)
        self.multi_select_menu.add_command(label="剪切", command=self.cut_item)
        self.multi_select_menu.add_separator()
        self.multi_select_menu.add_command(label="删除", command=self.delete_selected_image)
        self.multi_select_menu.add_separator()
        self.multi_select_menu.add_command(label="识图区域", command=self.image_rc_area)
        self.multi_select_menu.add_command(label="偏移坐标", command=self.offset_coords)
        self.multi_select_menu.add_separator()
        self.multi_select_menu.add_command(label="清空列表", command=self.clear_list)
        self.multi_select_menu.add_separator()
        self.multi_select_menu.add_command(label="查看日志", command=self.show_logs)
        self.multi_select_menu.add_command(label="检查更新", command=self.check_update)


    def update_context_menu(self):
        selected = self.tree.selection()
        if selected:
            selected_item = selected[0]
            values = self.tree.item(selected_item, "values")
            
            # 更新识图功能菜单项
            if values and len(values) > 2:
                try:
                    similarity = float(values[2])
                    new_label = "关闭识图" if similarity > 0 else "开启识图"
                    new_cmd = self.Normal_click if similarity > 0 else self.Image_recognition_click
                    self.context_menu.entryconfig(1, label=new_label, command=new_cmd)
                except ValueError:
                    print("相似度解析错误")
            
            # 更新禁用/启用菜单项（基于“状态”列）
            disabled = self.item_is_disabled(selected_item)
            new_disable_label = "启用" if disabled else "禁用"
            self.context_menu.entryconfig(10, label=new_disable_label, command=self.toggle_disable_status)
            self.update_label() # 更新详细信息
    
    def toggle_disable_status(self):
        selected = self.tree.selection()
        if selected:
            selected_item = selected[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]  # 获取原始数据

            # 切换状态（索引8），保持其他字段不变，且【需禁用】（索引9）不变
            new_status = "禁用" if selected_image[8] != "禁用" else "启用"
            
            # 创建更新后的元组（通过切片和拼接）
            updated_image = (
                *selected_image[:8],  # 前8个元素
                new_status,           # 新的状态值（替换第8个元素）
                *selected_image[9:]   # 第9个元素之后的
            )

            # 更新数据源
            self.image_list[selected_index] = updated_image

            # 更新 TreeView 项
            values = (os.path.basename(updated_image[0]),) + updated_image[1:]
            self.tree.item(selected_item, values=values)

            self.update_context_menu()
            self.update_image_listbox()
            # —— 强制清除所有选中和焦点 —— 
            self.tree.selection_remove(self.tree.selection())

    def item_is_disabled(self, item):
        values = self.tree.item(item, "values")
        if len(values) > 8 and values[8] == "禁用":
            self.tree.item(item, tags=("disabled",))
            return True
        else:
            # 如果项目未禁用，清除标签（如果需要）
            self.tree.item(item, tags=())
            return False
    
    def toggle_click_label(self):
        self.update_context_menu()  # 右键菜单更新
        self.update_image_listbox()

    def start_from_step(self):
        self.from_step = True
        if not self.running:
            self.toggle_script()  
        else:
            messagebox.showinfo("提示", "请先点击【停止运行(F9)】")

    def open_image_location(self):
        selected_items = self.tree.selection() 
        if not selected_items:
            messagebox.showinfo("提示", "请先选择一个步骤！")
            return

        try:
            # 获取选中项的索引（假设 tree 的 item ID 与 image_list 索引一致）
            selected_index = self.tree.index(selected_items[0])
            img_data = self.image_list[selected_index]
            image_path = img_data[0]  # 图片路径在 img_data[0]

            if not image_path:
                messagebox.showwarning("警告", "图片路径为空！")
                return

            # 转换为绝对路径（确保路径格式正确）
            abs_path = os.path.abspath(image_path)

            if not os.path.exists(abs_path):
                messagebox.showwarning("警告", f"图片路径不存在！\n路径: {abs_path}")
                return

            # Windows 下使用 `explorer /select` 打开文件夹并选中文件
            subprocess.Popen(f'explorer /select,"{abs_path}"', shell=True)

        except IndexError:
            messagebox.showwarning("警告", "找不到对应的图片数据！")
        except Exception as e:
            messagebox.showerror("错误", f"打开图片位置时出错:\n{str(e)}")

    def show_context_menu(self, event):
        item = self.tree.identify_row(event.y)

        if item:  # 点击的是项目
            # 获取当前所有选中的项
            selected_items = self.tree.selection()

            # 判断是否是多选状态
            if item not in selected_items or len(selected_items) <= 1:
                # 如果点击的不是当前选中的项，或选中的项数 <= 1，则重设选中项
                self.tree.selection_clear()
                self.tree.selection_set(item)
                self.tree.focus(item)
                selected_items = (item,)

            # 根据选中项数显示不同菜单
            if len(selected_items) > 1:
                self.root.after(1, lambda: self.multi_select_menu.post(event.x_root, event.y_root))
            else:
                self.update_context_menu()
                self.root.after(1, lambda: self.context_menu.post(event.x_root, event.y_root))
        else:  # 点击的是空白处
            # —— 强制清除所有选中和焦点 —— 
            self.tree.selection_remove(self.tree.selection())
            self.empty_space_menu.post(event.x_root, event.y_root)

        return "break"
   
    def clear_list(self):
        self.reset_to_initial_state()

    def create_image_copy_and_stepname(self, original_path, original_stepname):
        dirname = os.path.dirname(original_path)
        base_name = os.path.basename(original_path)
        name, ext = os.path.splitext(base_name)

        m = re.match(r"^(.*)_(\d+)$", name)
        base = m.group(1) if m else name

        sm = re.match(r"^(.*)_(\d+)$", original_stepname)
        step_base = sm.group(1) if sm else original_stepname

        count = 1
        while True:
            new_file_name = f"{base}_{count}{ext}"
            new_step_name = f"{step_base}_{count}"
            new_path = os.path.join(dirname, new_file_name)

            if not os.path.exists(new_path) and not self.stepname_exists(new_step_name):
                break
            count += 1

        shutil.copy2(original_path, new_path)
        return new_path, new_step_name

    def stepname_exists(self, name):
        return any(img[1] == name for img in self.image_list + self.copied_items)
 
    def copy_item(self):
        if self.is_cut_mode:
            self.restore_cut()
            messagebox.showinfo("提示", "已恢复剪切后未粘贴的步骤，请重新复制")
            return

        selected = self.tree.selection()
        if not selected:
            return

        self.is_cut_mode = False
        self.cut_original_indices = []
        self.copied_items = []

        for sel in selected:
            idx = self.tree.index(sel)
            original = self.image_list[idx]

            # 注意：这里只是保存原始引用，用于粘贴时再复制
            self.copied_items.append(original)

        print(f"已复制 {len(self.copied_items)} 个项目")
        self.tree.selection_clear()
        self.tree.selection_remove(self.tree.selection())
     
    def cut_item(self):
        selected = self.tree.selection()
        if not selected:
            messagebox.showinfo("提示", "请先选择要剪切的项目")
            return

        self.is_cut_mode = True
        self.cut_original_indices.clear()
        self.copied_items.clear()

        # 收集选中项索引并倒序删除
        indices = sorted((self.tree.index(iid) for iid in selected), reverse=True)
        for idx in indices:
            self.cut_original_indices.append(idx)
            self.copied_items.insert(0, self.image_list.pop(idx))  # 保持顺序

        self.update_image_listbox()
        self.clear_labels()

        # —— 强制清除所有选中和焦点 —— 
        self.tree.selection_remove(self.tree.selection())

        print(f"已剪切 {len(self.copied_items)} 个项目")

    def paste_item(self):
        if not self.copied_items:
            messagebox.showinfo("提示", "没有要粘贴的项目")
            return

        # 计算插入位置
        focus = self.tree.focus()
        insert_pos = self.tree.index(focus) + 1 if focus else len(self.image_list)

        new_records = []
        for record in self.copied_items:
            original_path = record[0]
            original_stepname = record[1]
            dirname = os.path.dirname(original_path)
            base_name = os.path.basename(original_path)
            name, ext = os.path.splitext(base_name)

            # 提取 base 名（去除 _数字 后缀）
            match = re.match(r"^(.*?)(?:_(\d+))?$", name)
            base = match.group(1) if match else name

            step_match = re.match(r"^(.*?)(?:_(\d+))?$", original_stepname)
            step_base = step_match.group(1) if step_match else original_stepname

            if self.is_cut_mode:
                # 剪切模式：保留文件名和步骤名
                new_path = original_path
                new_step_name = original_stepname
                new_record = [new_path, new_step_name] + list(record[2:])
                os.rename(original_path, new_path)  # 实际路径相同，可省略
                new_records.append(new_record)  # ✅ 加上这句
            else:
                # 复制模式：添加递增后缀
                count = 1
                while True:
                    new_file_name = f"{base}_{count}{ext}"
                    new_step_name = f"{step_base}_{count}"
                    new_path = os.path.join(dirname, new_file_name)

                    if not os.path.exists(new_path) and not self.stepname_exists(new_step_name):
                        break
                    count += 1

                shutil.copy2(original_path, new_path)
                new_record = [new_path, new_step_name] + list(record[2:])
                new_records.append(new_record)  # ✅ 加上这句

        # 插入到数据列表
        for i, record in enumerate(new_records):
            self.image_list.insert(insert_pos + i, record)

        # 刷新界面并聚焦
        self.update_image_listbox()
        new_iids = self.tree.get_children()[insert_pos: insert_pos + len(new_records)]
        if new_iids:
            self.tree.selection_set(new_iids)
            self.tree.focus(new_iids[0])
            self.tree.see(new_iids[-1])

        if self.is_cut_mode:
            self.cut_original_indices.clear()
            self.copied_items.clear()

        self.is_cut_mode = False
        print("粘贴完成")

    def restore_cut(self):
        """
        如果剪切后未粘贴就切换模式或关闭
        把被剪切的项目按原始位置恢复到列表和界面。
        """
        if not self.is_cut_mode or not self.copied_items:
            return

        # 按升序把项目放回去
        for idx, record in sorted(zip(self.cut_original_indices, self.copied_items)):
            self.image_list.insert(idx, record)

        # 刷新列表
        self.update_image_listbox()

        self.is_cut_mode = False
        self.cut_original_indices.clear()
        self.copied_items.clear()

        print("剪切操作已恢复，原始项目已还原")

    def edit_similarity_threshold(self):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        dialog = tk.Toplevel(self.root)
        dialog.withdraw()                     # 先隐藏
        dialog.title("修改相似度")
        dialog.transient(self.root)
        dialog.grab_set()

        # 标签和输入框
        label = tk.Label(dialog, text="请输入新的相似度（0 - 1.0）")
        label.pack(padx=10, pady=10)
        
        entry = tk.Entry(dialog)
        entry.pack(padx=10, pady=5)
        entry.insert(0, str(selected_image[2]))

        # 保存和取消按钮
        button_frame = tk.Frame(dialog)
        button_frame.pack(pady=10)

        def on_save():
            try:
                new_similarity = float(entry.get())
                if not 0 <= new_similarity <= 1.0:
                    raise ValueError
            except ValueError:
                messagebox.showerror("错误", "请输入0到1.0之间的有效数值。", parent=dialog)
                return

            self.image_list[selected_index] = (
                selected_image[0],  # 图片路径
                selected_image[1],  # 步骤名称
                new_similarity,     # 新的相似度阈值
                *selected_image[3:]  # 剩余字段
            )
            self.update_image_listbox()
            dialog.destroy()

        # 在创建按钮时添加bootstyle参数
        save_button = ttk.Button(
            button_frame, 
            text="保存", 
            command=on_save,
            bootstyle="primary-outline"  # 主要轮廓样式
        )
        save_button.pack(side=tk.RIGHT, padx=5)

        cancel_button = ttk.Button(
            button_frame, 
            text="取消", 
            command=dialog.destroy,
            bootstyle="primary-outline" 
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)

        # 让 Tkinter 计算理想大小
        dialog.update_idletasks()
        w = dialog.winfo_reqwidth()
        h = dialog.winfo_reqheight()

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - w) // 2
        y = main_y + (main_h - h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{w}x{h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")

    def edit_wait_time(self, event=None):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        self.tree.see(selected_item)
        self.tree.update_idletasks()
        bbox = self.tree.bbox(selected_item, column='#2') 
        if not bbox:
            return

        x, y, width, height = bbox
        values = self.tree.item(selected_item, 'values')
        current_value = values[5] if len(values) > 5 else ""

        entry = tk.Entry(self.tree)
        entry.place(x=x, y=y, width=width, height=height)
        entry.insert(0, current_value)
        entry.select_range(0, tk.END)
        entry.focus()

        def on_save(event=None):
            try:
                new_wait_time = int(entry.get().strip())
            except ValueError:
                messagebox.showerror("错误", "请输入有效的整数")
                entry.focus()
                return

            if new_wait_time == selected_image[5]:
                entry.destroy()
                return

            # 更新 image_list
            self.image_list[selected_index] = (
                *selected_image[:5],     # 保留索引 0-4
                new_wait_time,           # 更新索引 5
                *selected_image[6:]      # 保留索引 6 以后
            )

            # 更新 Treeview
            all_values = list(self.tree.item(selected_item, 'values'))
            if len(all_values) > 5:
                all_values[5] = str(new_wait_time)
                self.tree.item(selected_item, values=all_values)

            self.update_image_listbox()
            entry.destroy()

        entry.bind('<FocusOut>', on_save)

    def on_treeview_double_click(self, event):
        """根据双击的列决定调用哪个编辑函数"""
        rowid = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)  # 如 '#0', '#1', '#2', ...

        if not rowid or not col:
            return

        if col == '#1':  
            self.edit_step_name(event)
        elif col == '#2':  
            self.edit_wait_time(event)

    def Normal_click(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]
            # 直接将相似度设置为 0
            new_similarity_threshold = 0.0
            # 更新 selected_image 中的相似度
            self.image_list[selected_index] = (
                selected_image[0],  # 图片路径
                selected_image[1],  # 步骤名称
                new_similarity_threshold,  # 新的相似度
                *selected_image[3:]  # 其余字段
            )
            # 更新界面显示
            self.update_image_listbox()

    def Image_recognition_click(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]
            # 直接将相似度设置为 0.8
            new_similarity_threshold = 0.8
            # 更新 selected_image 中的相似度
            self.image_list[selected_index] = (
                selected_image[0],  # 图片路径（索引 0）
                selected_image[1],  # 步骤名称（索引 1）
                new_similarity_threshold,  # 新的相似度（索引 2）
                *selected_image[3:]  # 剩余所有字段
            )
           
            # 更新界面显示
            self.update_image_listbox()
    
    def image_rc_area(self):
        self.rc_area_dialog = True
        need_disable = False
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()

        dialog = tk.Toplevel(self.root)
        dialog.withdraw()
        dialog.title("设置识图区域")
        dialog.transient(self.root)
        dialog.grab_set()

        selected_items = self.tree.selection()
        if not selected_items:
            return
        
        selected_items_indices = []

        for sel in selected_items:
            idx = self.tree.index(sel)
            selected_image = self.image_list[idx]
            selected_items_indices.append((idx, selected_image))

        if len(selected_items_indices) == 1:
            original_area_str = selected_items_indices[0][1][14]
            # 解析字符串
            coords, area_choice_value, img_coords = original_area_str.split("|")
            area_choice = tk.StringVar(value=area_choice_value)
        else:
            area_choice = tk.StringVar(value="1")  # 设置一个不存在的值，不匹配任何选项
            need_disable = True

        frame_opts = tk.Frame(dialog)
        frame_opts.pack(padx=10, pady=10, anchor='w')

        rb1 = tk.Radiobutton(frame_opts, text="步骤图片", variable=area_choice, value='screenshot')
        rb2 = tk.Radiobutton(frame_opts, text="全屏", variable=area_choice, value='fullscreen')
        rb3 = tk.Radiobutton(frame_opts, text="自定义", variable=area_choice, value='manual', command=lambda: open_manual_overlay())

        rb1.pack(side='left')
        rb2.pack(side='left', padx=(10, 0))
        rb3.pack(side='left', padx=(10, 0))

        btn_manual = ttk.Button(
            dialog, 
            text="框选识图区域", 
            width=10,
            command=lambda: (area_choice.set('manual'), open_manual_overlay()),
            bootstyle="primary-outline"
        )
        btn_manual.pack(padx=10, pady=(0, 10), fill='x', expand=True)

        frame_buttons = tk.Frame(dialog)
        frame_buttons.pack(padx=10, pady=(0, 10), fill='x', expand=True)

        def on_save():
            choice = area_choice.get()
            for idx, selected_image in selected_items_indices:
                # 解析当前项区域字符串（防止格式不一致，也可以都用统一初始值）
                old_coords, area_choice_value, img_coords = selected_image[14].split("|")
                img_left, img_top, img_right, img_bottom = map(int, img_coords.split(","))

                # 根据选择模式创建对应的区域字符串
                if choice == 'fullscreen':
                    # 全屏模式: 主区域全屏，步骤图片也全屏
                    new_area_str = f"0,0,{screen_w},{screen_h}|fullscreen|{img_left},{img_top},{img_right},{img_bottom}"
                elif choice == 'manual':
                    # 手动模式 - 直接从当前坐标获取
                    l, t, r, b = map(int, coords.split(','))  # 手动范围区域
                    new_area_str = f"{l},{t},{r},{b}|manual|{img_left},{img_top},{img_right},{img_bottom}"
                else:
                    # 默认步骤图片模式
                    new_area_str = f"{img_left},{img_top},{img_right},{img_bottom}|screenshot|{img_left},{img_top},{img_right},{img_bottom}"

                new_image = list(self.image_list[idx])
                new_image[14] = new_area_str
                step_name = new_image[1]
                self.image_list[idx] = tuple(new_image)
                logging.info(f"【{step_name}】识图区域更新: ({old_coords}) → ({img_left},{img_top},{img_right},{img_bottom})")
                print(f"【{step_name}】识图区域更新: ({old_coords}) → ({img_left},{img_top},{img_right},{img_bottom})")

            dialog.destroy()
            self.rc_area_dialog = False
            self.update_image_listbox()

        def on_cancel():
            dialog.destroy()
            self.rc_area_dialog = False

        btn_cancel = ttk.Button(frame_buttons, text="取消", command=on_cancel, bootstyle="primary-outline")
        btn_save = ttk.Button(frame_buttons, text="保存", command=on_save, bootstyle="primary-outline")

        btn_cancel.pack(side='left', expand=True, fill='x', padx=(0, 5))
        btn_save.pack(side='right', expand=True, fill='x', padx=(5, 0))

        if need_disable:
            rb3.config(state="disabled")  # 禁用 Radiobutton
            btn_manual.config(state="disabled")  # 禁用 Button
            need_disable = False

        old_coords, area_choice_value, img_coords = selected_image[14].split("|")       
        if area_choice_value == 'update':
            messagebox.showinfo("提示", f"检测到旧版本的配置文件\n请先完整运行完一次所有步骤，才可设置识图区域")
            rb1.config(state="disabled")
            rb2.config(state="disabled")
            rb3.config(state="disabled")
            btn_manual.config(state="disabled")
            btn_save.config(state="disabled")

        dialog.update_idletasks()
        w = dialog.winfo_reqwidth()
        h = dialog.winfo_reqheight()
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - w) // 2
        y = main_y + (main_h - h) // 2
        dialog.geometry(f"{w}x{h}+{x}+{y}")
        dialog.deiconify()
        dialog.iconbitmap("icon/app.ico")

        def open_manual_overlay():
            self.root.withdraw()
            # 给足时间用来隐藏主窗口
            self.root.after(200, _after_hide_window)

        def _after_hide_window():
            left, top, right, bottom = map(int, coords.split(","))
            if left == 0 and top == 0 and right == screen_w and bottom == screen_h:
                # 全屏模式使用默认居中区域
                default_w = int(screen_w//5)
                default_h = int(screen_h//5)
                initial_area = [
                    max((screen_w - default_w)//2, 0),
                    max((screen_h - default_h)//2, 0),
                    min((screen_w + default_w)//2, screen_w),
                    min((screen_h + default_h)//2, screen_h),
                ]
            else:
                initial_area = list(map(int, coords.split(",")))

            # 1️⃣ 整屏截图
            screenshot_img = ImageGrab.grab()
            screenshot_tk = ImageTk.PhotoImage(screenshot_img)
            
            # 2️⃣ 创建覆盖层
            overlay = tk.Toplevel(self.root)
            overlay.overrideredirect(True)
            overlay.attributes('-topmost', True)
            overlay.geometry(f"{screen_w}x{screen_h}+0+0")
            overlay.grab_set()
            
            # 3️⃣ 创建Canvas和初始蓝框
            canvas = tk.Canvas(overlay, width=screen_w, height=screen_h, highlightthickness=0)
            canvas.pack(fill='both', expand=True)
            canvas.create_image(0, 0, image=screenshot_tk, anchor='nw')
            
            # 使用initial_area创建初始蓝框
            rect_id = canvas.create_rectangle(
                initial_area[0], initial_area[1], initial_area[2], initial_area[3],
                outline='#0773fc', width=2
            )

            # 4️⃣ 按钮排除列表、手柄列表等
            button_exclusion_areas = []  # 存放每次 place_buttons 后按钮背景的 bbox
            items_ok = []
            items_no = []
            handle_ids = []

            # 用于管理遮罩的 image id
            overlay_image_id = None

            # 创建遮罩：半透明灰，挖掉选区和按钮区域
            def create_overlay():
                nonlocal overlay_image_id
                # 删除旧遮罩
                if overlay_image_id is not None:
                    canvas.delete(overlay_image_id)
                    overlay_image_id = None
                # 获取选区坐标
                l, t, r, b = map(int, canvas.coords(rect_id))
                # 创建 RGBA 图像，全图半透明黑
                mask = Image.new('RGBA', (screen_w, screen_h), (0, 0, 0, 128))
                draw = ImageDraw.Draw(mask)
                # 挖掉选区：全透明
                draw.rectangle([l, t, r, b], fill=(0, 0, 0, 0))
                # 挖掉按钮区域（如果希望按钮背后不被暗化，也可挖掉）
                for excl in button_exclusion_areas:
                    ex1, ey1, ex2, ey2 = excl
                    draw.rectangle([ex1, ey1, ex2, ey2], fill=(0, 0, 0, 0))
                # 转为 PhotoImage 并保留引用
                overlay_tk = ImageTk.PhotoImage(mask)
                overlay._overlay_img = overlay_tk  # 保持引用，防止被回收
                # 在 Canvas 上显示遮罩图像
                overlay_image_id = canvas.create_image(0, 0, image=overlay_tk, anchor='nw')
                # 确保蓝框、手柄、按钮在最上层
                canvas.tag_raise(rect_id)
                for hid in handle_ids:
                    canvas.tag_raise(hid)
                for iid in items_no + items_ok:
                    canvas.tag_raise(iid)

            # 初始创建遮罩
            create_overlay()

            # 5️⃣ √ / x 小按钮
            btn_size = 20
            offset   = 5          # 距蓝框偏移
            confirm_tag = 'btn_ok'
            cancel_tag  = 'btn_no'

            def draw_small_btn(x, y, tag, text):
                bg = canvas.create_rectangle(x, y, x+btn_size, y+btn_size,
                                            fill='white', outline='black', tags=tag)
                txt = canvas.create_text(x+btn_size/2, y+btn_size/2,
                                        text=text, tags=tag)
                return [bg, txt]

            def place_buttons():
                # 删除旧按钮
                for iid in items_ok + items_no:
                    canvas.delete(iid)
                items_ok.clear(); items_no.clear()
                # 计算按钮位置
                l, t, r, b = canvas.coords(rect_id)
                total_width = btn_size * 2 + 10
                x_base = max(r - total_width, 0)
                y_base = min(b + offset, screen_h - btn_size)
                x_x, x_y = x_base, y_base
                check_x, check_y = x_base + btn_size + 10, y_base
                items_no.extend(draw_small_btn(x_x, x_y, cancel_tag, 'x'))
                items_ok.extend(draw_small_btn(check_x, check_y, confirm_tag, '√'))
                # 更新排除区：用于遮罩挖洞
                button_exclusion_areas.clear()
                for bg_id in ([items_no[0]] if items_no else []) + ([items_ok[0]] if items_ok else []):
                    bbox = canvas.bbox(bg_id)
                    if bbox:
                        button_exclusion_areas.append(tuple(bbox))

            place_buttons()

            # 6️⃣ 手柄设置
            handle_radius = 5

            def update_resize_handles():
                # 清除旧的 handles
                for hid in handle_ids:
                    canvas.delete(hid)
                handle_ids.clear()
                # 获取矩形当前坐标
                l, t, r, b = canvas.coords(rect_id)
                # 四边中点 & 四角
                mid_top    = ((l + r) / 2, t)
                mid_bottom = ((l + r) / 2, b)
                mid_left   = (l, (t + b) / 2)
                mid_right  = (r, (t + b) / 2)
                corners = [(l, t), (r, t), (l, b), (r, b)]
                points = [mid_top, mid_right, mid_bottom, mid_left] + corners
                for cx, cy in points:
                    x0, y0 = cx - handle_radius, cy - handle_radius
                    x1, y1 = cx + handle_radius, cy + handle_radius
                    hid = canvas.create_oval(x0, y0, x1, y1,
                                            fill='#0773fc', outline='')
                    handle_ids.append(hid)

            update_resize_handles()

            # 7️⃣ 区域判断（边缘 / 内部），设置光标
            edge_th, min_size = 10, 20
            drag_data = dict(action=None, start_x=0, start_y=0, orig=[0,0,0,0])

            def detect_region(x, y):
                l,t,r,b = canvas.coords(rect_id)
                if abs(x-l)<=edge_th and abs(y-t)<=edge_th: return 'nw'
                if abs(x-r)<=edge_th and abs(y-t)<=edge_th: return 'ne'
                if abs(x-l)<=edge_th and abs(y-b)<=edge_th: return 'sw'
                if abs(x-r)<=edge_th and abs(y-b)<=edge_th: return 'se'
                if abs(x-l)<=edge_th and t+edge_th<y<b-edge_th: return 'w'
                if abs(x-r)<=edge_th and t+edge_th<y<b-edge_th: return 'e'
                if abs(y-t)<=edge_th and l+edge_th<x<r-edge_th: return 'n'
                if abs(y-b)<=edge_th and l+edge_th<x<r-edge_th: return 's'
                if l+edge_th < x < r-edge_th and t+edge_th < y < b-edge_th: return 'inside'
                return None

            def update_cursor(region):
                mapping = {
                    'n':'sb_v_double_arrow','s':'sb_v_double_arrow',
                    'w':'sb_h_double_arrow','e':'sb_h_double_arrow',
                    'nw':'size_nw_se','se':'size_nw_se',
                    'ne':'size_ne_sw','sw':'size_ne_sw',
                    'inside':'fleur'
                }
                canvas.config(cursor=mapping.get(region,''))

            # 8️⃣ 事件处理：仅在 release 时更新遮罩
            def on_mv(event):
                if drag_data['action'] is None:
                    update_cursor(detect_region(event.x, event.y))

            def on_press(event):
                # 如果点到 √ / x，让它自然触发按钮回调，不隐藏
                item = canvas.find_withtag('current')
                if item:
                    if confirm_tag in canvas.gettags(item): return
                    if cancel_tag  in canvas.gettags(item): return
                region = detect_region(event.x, event.y)
                drag_data['action'] = 'move' if region=='inside' else region
                drag_data['start_x'] = event.x
                drag_data['start_y'] = event.y
                drag_data['orig']    = canvas.coords(rect_id)
                # 如果确定是拖拽区域（move 或 resize 区域），隐藏按钮并删除遮罩
                if drag_data['action'] is not None:
                    # 删除按钮显示
                    for iid in items_ok + items_no:
                        canvas.delete(iid)
                    items_ok.clear()
                    items_no.clear()
                    # 清空排除区
                    button_exclusion_areas.clear()
                    # 删除遮罩图像
                    nonlocal_overlay_id = overlay_image_id  # 仅为说明，实际删除：
                    if overlay_image_id is not None:
                        canvas.delete(overlay_image_id)
                    # 不再调用 create_overlay()

            def on_drag(event):
                action = drag_data['action']
                if not action: return
                dx = event.x - drag_data['start_x']
                dy = event.y - drag_data['start_y']
                l0,t0,r0,b0 = drag_data['orig']
                l,t,r,b = l0,t0,r0,b0
                if action == 'move':
                    l,r = l0+dx, r0+dx
                    t,b = t0+dy, b0+dy
                    # 边界限定
                    if l<0: r -= l; l=0
                    if t<0: b -= t; t=0
                    if r>screen_w: l -= (r-screen_w); r=screen_w
                    if b>screen_h: t -= (b-screen_h); b=screen_h
                else:
                    if 'n' in action:
                        t = max(0, min(t0+dy, b0-min_size))
                    if 's' in action:
                        b = min(screen_h, max(b0+dy, t0+min_size))
                    if 'w' in action:
                        l = max(0, min(l0+dx, r0-min_size))
                    if 'e' in action:
                        r = min(screen_w, max(r0+dx, l0+min_size))
                canvas.coords(rect_id, l, t, r, b)
                # 拖拽过程中只更新手柄，不重绘按钮或遮罩
                update_resize_handles()
                # 不调用 create_overlay()

            def on_release(event):
                drag_data['action'] = None
                # 拖拽结束，重新绘制按钮
                place_buttons()
                # 更新手柄
                update_resize_handles()
                # 拖拽结束后再更新遮罩
                create_overlay()

            canvas.bind('<Motion>', on_mv)
            canvas.bind('<ButtonPress-1>', on_press)
            canvas.bind('<B1-Motion>', on_drag)
            canvas.bind('<ButtonRelease-1>', on_release)

            # 9️⃣ "√ / x" 逻辑
            def confirm_and_close():
                l,t,r,b = map(int, canvas.coords(rect_id))
                nonlocal coords
                coords = f"{l},{t},{r},{b}"
                overlay.grab_release()
                overlay.destroy()
                self.root.deiconify()

            def cancel_and_close():
                overlay.grab_release()
                overlay.destroy()
                self.root.deiconify()

            # √ / x 点击事件绑定
            canvas.tag_bind(confirm_tag, '<Button-1>', lambda e: confirm_and_close())
            canvas.tag_bind(cancel_tag,  '<Button-1>', lambda e: cancel_and_close())

            # Esc 键 = 取消
            overlay.bind_all('<Key-Escape>', lambda e: cancel_and_close())

            # 保存引用，防止 screenshot_tk 被垃圾回收
            overlay._bg_img = screenshot_tk

    def edit_step_name(self, event=None):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        self.tree.see(selected_item)
        self.tree.update_idletasks()
        bbox = self.tree.bbox(selected_item, column='#1')  # 第2列，索引是1
        if not bbox:
            return

        x, y, width, height = bbox
        values = self.tree.item(selected_item, 'values')
        current_name = values[1] if len(values) > 1 else ""

        entry = tk.Entry(self.tree)
        entry.place(x=x, y=y, width=width, height=height)
        entry.insert(0, current_name)
        entry.select_range(0, tk.END)
        entry.focus()

        def on_save(event=None):
            new_name = entry.get().strip()
            if not new_name:
                messagebox.showerror("错误", "名称不能为空")
                entry.focus()
                return

            # 获取原始名称（假设 selected_items 是 Treeview 的选中项）
            original_name = values[1] if len(values) > 1 else ""  # 名称在第2列（索引1）

            if new_name == original_name:
                entry.destroy()
                return

            existing_names = [img[1] for img in self.image_list]
            if new_name in existing_names:
                m = re.match(r"^(.*)_(\d+)$", new_name)
                base = m.group(1) if m else new_name
                num = int(m.group(2)) if m else 1

                while True:
                    num += 1
                    candidate = f"{base}_{num}"
                    if candidate not in existing_names:
                        break

                answer = messagebox.askyesno(
                    "重命名确认",
                    f"列表已包含同名步骤，\n要将“{selected_image[1]}”重命名为“{candidate}”吗？"
                )
                if not answer:
                    entry.destroy()
                    return
                final_name = candidate
            else:
                final_name = new_name

            # 更新 image_list 主项
            new_image = list(selected_image)
            new_image[1] = final_name
            self.image_list[selected_index] = new_image

            # 🔁 遍历 self.image_list每项索引 7, 9, 12, 13
            for i, img_data in enumerate(self.image_list):
                img_list = list(img_data)  # 将元组转换为列表
                updated = False
                for idx in [7, 9, 12, 13]:
                    if len(img_list) > idx and img_list[idx] == original_name:
                        img_list[idx] = final_name
                        updated = True
                if updated:
                    self.image_list[i] = tuple(img_list)  # 修改后转回元组并赋值回原列表
            # 更新 Treeview 第2列
            all_values = list(self.tree.item(selected_item, 'values'))
            if len(all_values) > 1:
                all_values[1] = final_name
                self.tree.item(selected_item, values=all_values)

            self.update_image_listbox()
            entry.destroy()

        # 绑定回车保存
        entry.bind('<Return>', on_save)
        # 绑定焦点丢失保存
        entry.bind('<FocusOut>', on_save)
   
    def set_condition_jump(self):
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("警告", "请先选择一个项目")
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        # 复制一份可变的列表用于修改（原先是 tuple）
        selected_image = list(self.image_list[selected_index])

        # 创建对话框
        dialog = tk.Toplevel(self.root)
        dialog.withdraw()  # 先隐藏，等布局完成再展示
        dialog.title("设置条件判断")
        dialog.transient(self.root)
        dialog.grab_set()

        ##################
        # 条件选择（两列 Combobox）
        ##################
        condition_frame = tk.Frame(dialog)
        condition_frame.pack(pady=5)
        tk.Label(condition_frame, text="条件为:").pack(side=tk.LEFT)

        # 取出现有的两个条件值（如果没有则置为空）
        current_condition1 = selected_image[6] if len(selected_image) > 6 else ""
        current_condition2 = selected_image[11] if len(selected_image) > 11 else ""
        # 如果为空则显示“无”，否则就显示现有值
        condition_var1 = tk.StringVar(value="无" if not current_condition1 else current_condition1)
        condition_var2 = tk.StringVar(value="无" if not current_condition2 else current_condition2)
        conditon_value1 = ["识图成功", "无"]
        conditon_value2 = ["识图失败", "无"]

        # 第一个条件下拉框
        condition_combo1 = ttk.Combobox(
            condition_frame,
            textvariable=condition_var1,
            values=conditon_value1,
            width=12
        )
        condition_combo1.pack(side=tk.LEFT, padx=(0, 10))

        # 第二个条件下拉框
        condition_combo2 = ttk.Combobox(
            condition_frame,
            textvariable=condition_var2,
            values=conditon_value2,
            width=12
        )
        condition_combo2.pack(side=tk.LEFT)

        ##################
        # 跳转到选择（两列 Combobox）
        ##################
        jump_frame = tk.Frame(dialog)
        jump_frame.pack(pady=5)
        tk.Label(jump_frame, text="跳转到:").pack(side=tk.LEFT)

        # 生成所有步骤名称供下拉使用（第一个值固定为“无”）
        step_names = ["无"] + [img[1] for img in self.image_list if img[1]]
        step_names_2 = [img[1] for img in self.image_list if img[1]]

        # 取出现有的两个跳转值
        current_jump1 = selected_image[7] if len(selected_image) > 7 else ""
        current_jump2 = selected_image[12] if len(selected_image) > 12 else ""
        step_name = selected_image[1]
        jump_var1 = tk.StringVar(value="无" if not current_jump1 else current_jump1)
        jump_var2 = tk.StringVar(value= "无" if not current_jump2 else current_jump2)

        # 第一个跳转下拉框
        jump_combo1 = ttk.Combobox(
            jump_frame,
            textvariable=jump_var1,
            values=step_names,
            width=12
        )
        jump_combo1.pack(side=tk.LEFT, padx=(0, 10))

        # 第二个跳转下拉框
        jump_combo2 = ttk.Combobox(
            jump_frame,
            textvariable=jump_var2,
            values=step_names,
            width=12
        )
        jump_combo2.pack(side=tk.LEFT)

        ##################
        # 需禁用选择（两列 Combobox）
        ##################
        disable_frame = tk.Frame(dialog)
        disable_frame.pack(pady=5)
        tk.Label(disable_frame, text="需禁用:").pack(side=tk.LEFT)

        # 取出现有的两个禁用值
        current_disable1 = selected_image[9] if len(selected_image) > 9 else ""
        current_disable2 = selected_image[13] if len(selected_image) > 13 else ""
        disable_var1 = tk.StringVar(value="无" if not current_disable1 else current_disable1)
        disable_var2 = tk.StringVar(value="无" if not current_disable2 else current_disable2)

        # 第一个禁用下拉框
        disable_combo1 = ttk.Combobox(
            disable_frame,
            textvariable=disable_var1,
            values=step_names,
            width=12
        )
        disable_combo1.pack(side=tk.LEFT, padx=(0, 10))

        # 第二个禁用下拉框
        disable_combo2 = ttk.Combobox(
            disable_frame,
            textvariable=disable_var2,
            values=step_names,
            width=12
        )
        disable_combo2.pack(side=tk.LEFT)

        ##################
        # 逻辑绑定：
        # 1. 当 条件1 或 条件2 被设置为“无”时，自动将对应的跳转和禁用设为“无”
        # 2. 当 跳转1 或 禁用1 不为“无”时，强制将 条件1 设为“识图成功”；否则条件1 设为“无”
        #    同理：跳转2/禁用2 不为“无”时，强制将 条件2 设为“识图失败”；否则条件2 设为“无”
        ##################

        # —— 条件变为“无”时，重置对应的跳转和禁用 —— #
        def on_condition1_change(event):
            if condition_var1.get() == "无":
                jump_var1.set("无")
                disable_var1.set("无")

        def on_condition2_change(event):
            if condition_var2.get() == "无":
                jump_var2.set("无")
                disable_var2.set("无")

        condition_combo1.bind("<<ComboboxSelected>>", on_condition1_change)
        condition_combo2.bind("<<ComboboxSelected>>", on_condition2_change)

        # —— 跳转或禁用被设置后，调整对应的条件 —— #
        def update_condition1(_event=None):
            # 只要跳转1或禁用1有一个不为“无”，就设置条件1为“识图成功”，否则为“无”
            if jump_var1.get() != "无" or disable_var1.get() != "无":
                condition_var1.set("识图成功")
            else:
                condition_var1.set("无")

        def update_condition2(_event=None):
            # 只要跳转2或禁用2有一个不为“无”，就设置条件2为“识图失败”，否则为“无”
            if jump_var2.get() != "无" or disable_var2.get() != "无":
                condition_var2.set("识图失败")
            else:
                condition_var2.set("无")

        # 将回调函数绑定到跳转1、禁用1的选中事件
        jump_combo1.bind("<<ComboboxSelected>>", update_condition1)
        disable_combo1.bind("<<ComboboxSelected>>", update_condition1)

        # 将回调函数绑定到跳转2、禁用2的选中事件
        jump_combo2.bind("<<ComboboxSelected>>", update_condition2)
        disable_combo2.bind("<<ComboboxSelected>>", update_condition2)

        # 布局完成后再显示窗口
        dialog.deiconify()

        ##################
        # 保存回调函数（收集并写回 selected_image）
        ##################
        def save_condition():
            # 读取用户选择
            cond1 = condition_var1.get()
            cond2 = condition_var2.get()
            jump1 = jump_var1.get()
            jump2 = jump_var2.get()
            dis1 = disable_var1.get()
            dis2 = disable_var2.get()

            # 如果用户选了“无”，就映射为空字符串
            cond1 = "" if cond1 == "无" else cond1
            cond2 = "" if cond2 == "无" else cond2
            jump1 = "" if jump1 == "无" else jump1
            jump2 = "" if jump2 == "无" else jump2
            dis1 = "" if dis1 == "无" else dis1
            dis2 = "" if dis2 == "无" else dis2

            # 验证逻辑：如果不存在存在任意跳转或禁用，则清空条件
            if (cond1) and not (jump1 or dis1):
                cond1 = ""

            if (cond2) and not (jump2 or dis2):
                cond2 = ""

            try:
                # 确保 selected_image 列表长度
                while len(selected_image) < 15: #新增索引
                    selected_image.append("")

                # 将用户选择写回对应位置
                selected_image[6] = cond1
                selected_image[11] = cond2
                selected_image[7] = jump1
                selected_image[12] = jump2
                selected_image[9] = dis1
                selected_image[13] = dis2

                # 更新 self.image_list 中的元组
                self.image_list[selected_index] = tuple(selected_image)
                # 刷新界面上的列表显示
                self.update_image_listbox()

                # 重新选中刚才的项目，保持焦点
                items = self.tree.get_children()
                if selected_index < len(items):
                    self.tree.selection_set(items[selected_index])
                    self.tree.focus(items[selected_index])

                logging.info(
                    f"更新条件跳转设置：" 
                    f"条件1={cond1}, 条件2={cond2}, 跳转1={jump1}, 跳转2={jump2}, 禁用1={dis1}, 禁用2={dis2}"
                )
            except Exception as e:
                logging.error(f"保存条件跳转设置出错: {str(e)}")
                messagebox.showerror("错误", f"保存失败: {str(e)}", parent=dialog)
            finally:
                dialog.destroy()

        # 按钮框架
        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=10)

        # 在创建按钮时添加bootstyle参数
        save_button = ttk.Button(
            btn_frame, 
            text="保存", 
            command=save_condition,
            bootstyle="primary-outline"  # 主要轮廓样式
        )
        save_button.pack(side=tk.RIGHT, padx=5)

        cancel_button = ttk.Button(
            btn_frame, 
            text="取消", 
            command=dialog.destroy,
            bootstyle="primary-outline"  
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)

        # 让 Tkinter 计算“理想”大小
        dialog.update_idletasks()
        req_w = dialog.winfo_reqwidth()
        req_h = dialog.winfo_reqheight()

        # 目标比例 9:5
        ratio_w, ratio_h = 9, 5

        # 方案 A：以理想宽度 req_w 为基准，计算对应的高度
        h_based_on_w = int(req_w * ratio_h / ratio_w)
        # 方案 B：以理想高度 req_h 为基准，计算对应的宽度
        w_based_on_h = int(req_h * ratio_w / ratio_h)

        # 选择能包下所有控件的最小方案
        if h_based_on_w >= req_h:
            base_w, base_h = req_w, h_based_on_w
        else:
            base_w, base_h = w_based_on_h, req_h

        # 仅对水平边距应用最小边距
        min_margin = 5  # 单侧最小水平边距
        # 如果当前左右边距 < min_margin，则增补；否则保持按比例计算宽度
        if base_w - req_w < 2 * min_margin:
            final_w = req_w + 2 * min_margin
        else:
            final_w = base_w

        # 垂直方向使用按比例计算的高度，无最小边距限制
        final_h = base_h

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - final_w) // 2
        y = main_y + (main_h - final_h) // 2

        # 一次性设置大小和位置，并显示
        dialog.geometry(f"{final_w}x{final_h}+{x}+{y}")
        dialog.deiconify()
        dialog.iconbitmap("icon/app.ico")  # 设置窗口图标
   
    def on_treeview_select(self, event):
        """当 Treeview 选择改变时更新预览图像"""
        selected_items = self.tree.selection()
        if not selected_items:
            self.load_default_image()
            self.clear_labels()
            return

        selected_index = self.tree.index(selected_items[0])

        try:
            img_path = self.image_list[selected_index][0]
            original_image = Image.open(img_path)

            def _update_when_ready():
                w = self.preview_container.winfo_width() - 5
                h = self.preview_container.winfo_height() - 5

                if w < 10 or h < 10:
                    self.preview_container.after(100, _update_when_ready)
                    return

                original_w, original_h = original_image.size

                # 计算宽高比例
                width_ratio = w / original_w
                height_ratio = h / original_h

                # 目标是放大到至少铺满一个方向，但不能超过容器
                scale_ratio = max(width_ratio, height_ratio)
                final_w = int(original_w * scale_ratio)
                final_h = int(original_h * scale_ratio)

                # 再限制不能超过容器
                if final_w > w or final_h > h:
                    scale_ratio = min(w / final_w, h / final_h)
                    final_w = int(final_w * scale_ratio)
                    final_h = int(final_h * scale_ratio)

                resized = original_image.resize((final_w, final_h), Image.Resampling.LANCZOS)

                photo = ImageTk.PhotoImage(resized)
                self.preview_image_label.config(image=photo)
                self.preview_image_label.image = photo
                self.update_label()

            self.preview_container.after(100, _update_when_ready)

        except Exception as e:
            print(f"预览图像时出错: {e}")
            logging.error(f"预览图像时出错: {e}")
            self.preview_image_label.config(image='')

    def focus_on_step(self, index_or_event):
        """实现跟随步骤功能"""
        try:
            # 如果传入的是事件对象，可以根据需要提取索引，或者直接返回
            if hasattr(index_or_event, 'widget'):
                # 如果没有办法从事件对象中获取到索引，可以直接返回或进行其它处理
                return
            # 如果不是事件对象，那么就将其当作索引处理
            index = index_or_event
            items = self.tree.get_children()
            if 0 <= index < len(items):
                self.tree.selection_set(items[index])
                self.tree.focus(items[index])
                self.tree.see(items[index])
        except Exception as e:
            print(f"跟随步骤出错: {e}")
            logging.error(f"跟随步骤出错: {e}")

    def show_logs(self):
        """显示日志窗口（居中于主窗口）"""    
        log_window = tk.Toplevel(self.root)
        log_window.withdraw()                     # 先隐藏
        log_window.title("应用日志")
        log_window.transient(self.root)
        log_window.grab_set()
      
        # 创建文本框和滚动条
        text_frame = tk.Frame(log_window)
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = tk.Scrollbar(text_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        log_text = tk.Text(
            text_frame,
            wrap=tk.WORD,
            yscrollcommand=scrollbar.set,
            font=('Microsoft YaHei UI', 10)
        )
        log_text.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=log_text.yview)
        
        # 读取日志文件内容
        try:
            with open('app.log', 'rb') as f:  # 二进制模式
                content = f.read()
                try:
                    log_content = content.decode('utf-8')
                except UnicodeDecodeError:
                    log_content = content.decode('gbk', errors='replace')
            log_text.insert(tk.END, log_content)
            log_text.see(tk.END)  # 滚动到最后
        except FileNotFoundError:
            log_text.insert(tk.END, "日志文件不存在")
        except Exception as e:
            log_text.insert(tk.END, f"读取日志失败: {str(e)}")
        
        # 禁用文本框编辑
        log_text.config(state=tk.DISABLED)

        # 让 Tkinter 计算“理想”大小
        log_window.update_idletasks()
        req_w = log_window.winfo_reqwidth()
        req_h = log_window.winfo_reqheight()

        # 目标比例 4:3
        ratio_w, ratio_h = 4, 3

        # 方案 A：以理想宽度 req_w 为基准，计算对应的高度
        h_based_on_w = int(req_w * ratio_h / ratio_w)
        # 方案 B：以理想高度 req_h 为基准，计算对应的宽度
        w_based_on_h = int(req_h * ratio_w / ratio_h)

        # 选择能包下所有控件的最小方案
        # 如果 h_based_on_w >= req_h，就用 (req_w, h_based_on_w)，否则用 (w_based_on_h, req_h)
        if h_based_on_w >= req_h:
            new_w, new_h = req_w, h_based_on_w
        else:
            new_w, new_h = w_based_on_h, req_h

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_w = self.root.winfo_width()
        main_h = self.root.winfo_height()
        x = main_x + (main_w - new_w) // 2
        y = main_y + (main_h - new_h) // 2

        # 一次性设置大小（强制 4:3）和位置，并显示
        log_window.geometry(f"{new_w}x{new_h}+{x}+{y}")
        log_window.deiconify()

        log_window.iconbitmap("icon/app.ico")


if __name__ == "__main__":
    root = tk.Tk()
    app = ImageRecognitionApp(root)
    
    def on_closing():
        if app.is_cut_mode:
            app.restore_cut()
        if app.config_filename is None and app.image_list:
            response = tk.messagebox.askyesno(
                "提示",
                "未保存配置，是否保存？",
                parent=root
            )
            if response: 
                app.save_config()  
        root.destroy()
    
    root.protocol("WM_DELETE_WINDOW", on_closing)
    root.mainloop()
