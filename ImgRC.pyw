# -*- coding: utf-8 -*-
from pathlib import Path
import re
import subprocess
import tempfile
import tkinter as tk
from tkinter import filedialog, ttk, messagebox
from urllib.parse import urlparse
import zipfile
from PIL import Image, ImageTk, ImageGrab
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

CURRENT_VERSION = "v1.1.4" #版本号

def run_as_admin():
    if ctypes.windll.shell32.IsUserAnAdmin():
        return  # 已经是管理员，直接运行

    # 重新以管理员身份启动
    exe = sys.executable
    params = " ".join(sys.argv)
    ctypes.windll.shell32.ShellExecuteW(None, "runas", exe, params, None, 1)
    sys.exit()  # 退出当前进程，等待新进程执行

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
        self.image_list = []  # 存储 (图像路径, 步骤名称, 相似度, 键盘动作, 坐标(F2), 延时ms, 条件, 需跳转，状态， 需禁用， 鼠标动作)
        self.screenshot_area = None  # 用于存储截图区域
        self.rect = None  # 用于存储 Canvas 上的矩形
        self.start_x = None
        self.start_y = None
        self.canvas = None
        self.running = False  # 控制脚本是否在运行
        self.thread = None  # 用于保存线程
        self.hotkey = '<F9>'  # 开始/停止热键
        self.screenshot_hotkey = "F8"    # 固定截图热键
        self.similarity_threshold = 0.8  # 默认相似度阈值
        self.delay_time = 0.1  # 默认延迟时间
        self.loop_count = 1  # 默认循环次数
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

        # 区域B：树形区域
        self.region_b = tb.Frame(self.region_l)
        self.region_b.pack(fill=tk.BOTH, expand=True, padx=2, pady=5)

        # 使用 Treeview 来显示图片和延时ms
        self.tree = ttk.Treeview(self.region_b, columns=(
            "图片名称", "步骤名称", "相似度", "键盘动作", "坐标(F2)", "延时ms", "条件", "需跳转", "状态", "需禁用", "鼠标动作", "条件2", "需跳转2", "需禁用2"
        ), show='headings')
        self.tree.heading("图片名称", text="图片名称")
        self.tree.heading("步骤名称", text="步骤名称")
        self.tree.heading("相似度", text="相似度")
        self.tree.heading("键盘动作", text="键盘动作")
        self.tree.heading("坐标(F2)", text="坐标(F2)")
        self.tree.heading("延时ms", text="延时ms")
        self.tree.heading("条件", text="条件")
        self.tree.heading("需跳转", text="需跳转")
        self.tree.heading("状态", text="状态")
        self.tree.heading("需禁用", text="需禁用")
        self.tree.heading("鼠标动作", text="鼠标动作")
        self.tree.heading("条件2", text="条件2")
        self.tree.heading("需跳转2", text="需跳转2")
        self.tree.heading("需禁用2", text="需禁用2")

        # 设置列宽和对齐方式（居中）
        self.tree.column("图片名称", width=75, anchor='center')
        self.tree.column("步骤名称", width=75, anchor='center')
        self.tree.column("相似度", width=75, anchor='center')
        self.tree.column("键盘动作", width=75, anchor='center')
        self.tree.column("坐标(F2)", width=75, anchor='center')
        self.tree.column("延时ms", width=75, anchor='center')
        self.tree.column("条件", width=20, anchor='center')
        self.tree.column("需跳转", width=75, anchor='center')
        self.tree.column("状态", width=75, anchor='center')
        self.tree.column("需禁用", width=75, anchor='center')
        self.tree.column("鼠标动作", width=75, anchor='center')
        self.tree.column("条件2", width=75, anchor='center')
        self.tree.column("需跳转2", width=75, anchor='center')
        self.tree.column("需禁用2", width=75, anchor='center')

        # 1. 在 Treeview 上配置一个 hover 标签的样式
        self.tree.tag_configure('hover', background="#f3f3f3")  

        # 2. 用来记录上一次悬停的行
        self._prev_hover_row = None

        def safe_clear_tag(row_id):
            # 先确认该 item 还在 Treeview 里
            if row_id and self.tree.exists(row_id):
                self.tree.item(row_id, tags=())

        def on_motion(event):
            row_id = self.tree.identify_row(event.y)
            if row_id != self._prev_hover_row:
                # 清除之前行的 hover
                safe_clear_tag(self._prev_hover_row)
                # 给新行加 hover
                if row_id:
                    self.tree.item(row_id, tags=('hover',))
                self._prev_hover_row = row_id

        def on_leave2(event):
            # 鼠标移出时也清一次
            safe_clear_tag(self._prev_hover_row)
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
        self.region_c.pack(fill=tk.BOTH, padx=10, pady=(10, 0), expand=False)  # 关键修改

        # 设置目标宽度
        target_width = 357  # 可根据窗口动态计算或自定义设置
        target_height = int(target_width * 37 / 50)  # 宽高比

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
            width=target_width - 5, 
            height=target_height - 5,
            style="ImageContainer.TFrame"
        )
        self.preview_container.pack_propagate(False)
        self.preview_container.pack(pady=2, padx=2)

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

        # 详细信息标签区域
        # —— 第一行：标题 + 文件名 —— #
        self.label_frame = tk.Frame(self.region_d)
        self.label_frame.pack(fill="x",padx=10, pady=(20, 3))

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
        self.label_filename.pack(side="left")

        # —— 第二行：各字段标签 —— #
        self.labels_frame = tk.Frame(self.region_d)
        self.labels_frame.pack(fill="x", pady=(2, 0))

        # 初始化字段标签
        self.labels = {
            "图片名称": tk.Label(self.labels_frame, text="图片名称: ", anchor="w"),
            "相似度":   tk.Label(self.labels_frame, text="相似度: ",   anchor="w"),
            "坐标(F2)": tk.Label(self.labels_frame, text="坐标(F2): ", anchor="w"),
            "键盘动作": tk.Label(self.labels_frame, text="键盘动作: ", anchor="w"),
            "鼠标动作": tk.Label(self.labels_frame, text="鼠标动作: ", anchor="w"),
            "状态":     tk.Label(self.labels_frame, text="状态: ",     anchor="w"),
        }
        for lbl in self.labels.values():
            lbl.configure(foreground="#495057")
            lbl.pack(fill="x", padx=10, pady=0)
            
        # 绑定焦点事件
        self.tree.bind("<FocusIn>", self.update_label)

        # 绑定 F2 键获取鼠标位置
        self.root.bind('<F2>', self.get_mouse_position)  

        # 初始化上下文菜单
        self.tree.unbind('<Double-1>')
        self.tree.unbind('<Double-3>')
        self.tree.unbind('<Double-2>')

        # 为上下文菜单添加此绑定
        self.tree.bind('<Button-3>', self.show_context_menu)  # 右键点击
        self.tree.bind('<Button-1>', self.on_treeview_select)  # 左键点击

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
            # 基准分辨率和原始最大预览尺寸
            base_width = 1920
            base_height = 1080
            base_max_width = 290
            base_max_height = 220
            
            # 获取当前屏幕分辨率
            try:
                current_width = self.winfo_screenwidth()  # 尝试作为Tk窗口获取
            except AttributeError:
                current_width = base_width  # 回退到基准值
            try:
                current_height = self.winfo_screenheight()
            except AttributeError:
                current_height = base_height

            # 计算缩放比例
            scale = min(current_width / base_width, current_height / base_height)
            
            # 调整后的预览尺寸
            max_width = int(base_max_width * scale)
            max_height = int(base_max_height * scale)

            # 加载默认图像
            # 获取当前工作目录
            working_dir = os.getcwd()
            default_image_path = os.path.join(working_dir, "icon", "default_img.png")
            
            if os.path.exists(default_image_path):
                original_image = Image.open(default_image_path)
                
                # 获取原始尺寸
                original_width, original_height = original_image.size
                
                # 计算图像缩放比例
                width_ratio = max_width / original_width
                height_ratio = max_height / original_height
                scale_ratio = min(width_ratio, height_ratio)
                
                # 计算新的尺寸
                new_width = int(original_width * scale_ratio)
                new_height = int(original_height * scale_ratio)
                
                # 调整图像大小
                resized_image = original_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
                
                # 创建 PhotoImage 对象
                self.default_photo = ImageTk.PhotoImage(resized_image)
                
                # 更新预览标签
                self.preview_image_label.config(image=self.default_photo)
                self.preview_image_label.image = self.default_photo
            else:
                print("默认图片路径不存在:", default_image_path)
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

    def on_treeview_drag_motion(self, event):
        """拖动过程中高亮鼠标下方的项目"""
        if not hasattr(self, "dragged_item"):
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
        if not hasattr(self, "dragged_item"):
            return

        target_item = self.tree.identify_row(event.y)
        if target_item and target_item != self.dragged_item:
            dragged_index = self.tree.index(self.dragged_item)
            target_index = self.tree.index(target_item)

            # 获取拖动项的值
            dragged_values = self.tree.item(self.dragged_item, "values")
            dragged_image = self.image_list[dragged_index] if dragged_index < len(self.image_list) else None
            dragged_image_data = self.image_dict.get(self.dragged_item)

            # 删除原项
            self.tree.delete(self.dragged_item)
            del self.image_list[dragged_index]
            if self.dragged_item in self.image_dict:
                del self.image_dict[self.dragged_item]

            # 插入新项
            new_item = self.tree.insert("", target_index, values=dragged_values)
            self.image_list.insert(target_index, dragged_image)
            if dragged_image_data:
                self.image_dict[new_item] = dragged_image_data

            # 选中新项并更新预览
            self.tree.selection_set(new_item)
            self.dragged_item = new_item  # 更新拖动项引用以便预览函数识别
            self.on_treeview_select(None)
            self.update_image_listbox()
        self.dragged_item = None

    def update_label(self, event=None):
        """更新 Label 显示 Treeview 选中的隐藏列数据（带可靠的悬停提示功能）"""
        def 截断文本(文本, 最大长度=25):
            """辅助函数：当文本超过最大长度时添加省略号"""
            文本 = str(文本)
            return 文本[:最大长度-3] + "..." if len(文本) > 最大长度 else 文本

        class 悬停提示管理器:
            """管理悬停提示的创建和销毁"""
            def __init__(self, master):
                self.master = master
                self.当前提示 = None

            def 显示提示(self, 控件, 文本):
                self.隐藏提示()
                # 处理长文本换行
                if len(文本) > 37:
                    文本 = "\n".join(
                        文本[i:i+37] for i in range(0, len(文本), 37)
                    )
                # 使用传入的 master 作为父窗口
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
        # 初始化提示管理器时传入 root
        提示管理器 = 悬停提示管理器(self.root)

        # 先更新标题（在字段更新前执行一次）
        if getattr(self, 'config_filename', None):
            # 只取路径最后的文件名
            fname = os.path.basename(self.config_filename)
            self.label_filename.config(text=f"- {fname}")
        else:
            # 不显示
            self.label_filename.config(text="")
        # 字段配置 (名称: 索引)
        字段配置 = {
            "图片名称": 0, "相似度": 2, "坐标(F2)": 4,
            "键盘动作": 3, "鼠标动作": 10, "状态": 8
        }

        for 字段名, 索引 in 字段配置.items():
            raw = str(values[索引]).replace("\n", " ").strip()
            disp = 截断文本(raw)
            lbl = self.labels[字段名]

            # 取消所有旧绑定，并更新文本
            lbl.unbind("<Enter>")
            lbl.unbind("<Leave>")
            lbl.config(text=f"{字段名}:  {disp}")

            # 超长时才加提示
            if len(raw) > 25:
                lbl.bind(
                    "<Enter>",
                    lambda e, t=raw: 提示管理器.显示提示(e.widget, t)
                )
                lbl.bind(
                    "<Leave>",
                    lambda e: 提示管理器.隐藏提示()
                )

    def clear_labels(self):
        """清空 Label 内容"""
        # 清空各字段
        for key, lbl in self.labels.items():
            lbl.config(text=f"{key}: ")
        # 清空配置文件名（同一行）
        self.label_filename.config(text="")

    def register_global_hotkey(self):
        try:
            # 注册主功能热键
            def main_hotkey_callback():
                self.root.after(0, self.toggle_script)
                
            main_hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
            keyboard.add_hotkey(main_hotkey_str, main_hotkey_callback)
            
            # 注册截图热键（新增）
            def screenshot_hotkey_callback():
                self.root.after(0, self.prepare_capture_screenshot)
                
            keyboard.add_hotkey(self.screenshot_hotkey, screenshot_hotkey_callback)
            
            # 日志记录
            print("-" * 85)
            logging.info("-" * 85)
            print(f"主功能热键已注册：{self.hotkey}")
            print(f"截图热键已注册：{self.screenshot_hotkey}")
            logging.info("程序启动 - 热键注册完成")
            
        except Exception as e:
            print(f"注册热键失败: {e}")
            logging.error(f"热键注册失败: {e}")

    def unregister_global_hotkey(self):
        try:
            # 注销主热键
            main_hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
            keyboard.remove_hotkey(main_hotkey_str)
            
            # 注销截图热键（新增）
            keyboard.remove_hotkey(self.screenshot_hotkey)
            
            print(f"主功能热键已注销：{self.hotkey}")
            print(f"截图热键已注销：{self.screenshot_hotkey}")
            
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
        self.top.after(2000, self._auto_click_current_position)

    def _auto_click_current_position(self):
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
        # 记录起始点坐标
        self.start_x = event.x
        self.start_y = event.y
        # 如果有之前的矩形，删除
        if self.rect:
            self.canvas.delete(self.rect)
        # 删除已有的覆盖层（如果存在）
        if hasattr(self, 'overlay_rects'):
            for item in self.overlay_rects:
                self.canvas.delete(item)
        # 创建新的矩形框（初始为0尺寸）
        self.rect = self.canvas.create_rectangle(self.start_x, self.start_y, self.start_x, self.start_y, outline='#0773fc', width=2)
        # 初始化覆盖层列表
        self.overlay_rects = []

    def update_overlay(self, x1, y1, x2, y2):
        # 删除之前的覆盖层
        for item in self.overlay_rects:
            self.canvas.delete(item)
        self.overlay_rects = []
        # 获取画布的宽度和高度
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        # 定义选择区域的左上角和右下角
        left, top = min(x1, x2), min(y1, y2)
        right, bottom = max(x1, x2), max(y1, y2)
        
        # 创建四个覆盖层矩形，使矩形框外区域亮度下降（变暗）
        # 上面区域
        self.overlay_rects.append(
            self.canvas.create_rectangle(0, 0, w, top, fill='black', stipple='gray50', width=0)
        )
        # 左侧区域
        self.overlay_rects.append(
            self.canvas.create_rectangle(0, top, left, bottom, fill='black', stipple='gray50', width=0)
        )
        # 右侧区域
        self.overlay_rects.append(
            self.canvas.create_rectangle(right, top, w, bottom, fill='black', stipple='gray50', width=0)
        )
        # 底部区域
        self.overlay_rects.append(
            self.canvas.create_rectangle(0, bottom, w, h, fill='black', stipple='gray50', width=0)
        )

    def on_mouse_drag(self, event):
        # 动态更新矩形框的大小
        cur_x, cur_y = event.x, event.y
        self.canvas.coords(self.rect, self.start_x, self.start_y, cur_x, cur_y)
        # 同步更新覆盖层区域
        self.update_overlay(self.start_x, self.start_y, cur_x, cur_y)

    def on_button_release(self, event):
        # 记录终点坐标
        end_x, end_y = event.x, event.y
        dx = abs(end_x - self.start_x)
        dy = abs(end_y - self.start_y)
        threshold = 5  # 像素阈值，小于此值视为点击，不绘制
        # 如果设置了跳过标志，或者尺寸太小，则删除 rect 并返回
        if getattr(self, 'skip_next_draw', False):
            # 跳过本次绘制
            self.skip_next_draw = False
            if hasattr(self, 'rect') and self.rect:
                self.canvas.delete(self.rect)
                self.rect = None
            return
        if dx < threshold and dy < threshold:
            # 尺寸过小，删除刚创建的零尺寸矩形
            if hasattr(self, 'rect') and self.rect:
                self.canvas.delete(self.rect)
                self.rect = None
            return
        # 删除覆盖层，释放画布
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
                
                # 3. 创建更新后的数据元组
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
                    selected_image[13]      # 13: 需禁用2
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
                self.image_list.insert(insert_index, (screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次", "", "", ""))
            else:
                self.image_list.append((screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次", "", "", ""))

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

    def retake_screenshot(self):
        self.need_retake_screenshot = True     
        self.prepare_capture_screenshot()
   
    def update_image_listbox(self):
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
                    while len(full_item) < 14:
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
                    ) = full_item

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
        if self.config_filename and os.path.exists(self.config_filename):
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
                print(f"【{self.current_step_name}】执行完毕")
                logging.info(f"【{self.current_step_name}】执行完毕")
            self.current_loop += 1
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
        return match_result
   
    def stop_script(self):
        if self.thread is not None:
            # 设置停止标志（如果线程支持）
            self.running = False
            
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
        # 图像识别匹配
        # 获取当前步骤的完整信息
        selected_index = next((i for i, item in enumerate(self.image_list) if item[0] == template_path), None)
        if selected_index is not None:
            current_step = self.image_list[selected_index]
            mouse_coordinates = current_step[4]  # 获取鼠标坐标
            keyboard_input = current_step[3]  # 获取键盘输入
            step_name = current_step[1] #获取步骤名称
            similarity_threshold = current_step[2] #获取相似度
        else:
            mouse_coordinates = ""
            keyboard_input = ""
            step_name = ""
    
        # 获取屏幕截图
        screenshot = pyautogui.screenshot()
        screenshot = cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)
    
        # 检查模板图像是否存在
        if not os.path.exists(template_path):
            raise FileNotFoundError(f"【{step_name}】，找不到模板图像：{template_path}")
    
        # 读取模板图像（使用 cv2.imdecode 方式解决中文路径问题）
        with open(template_path, 'rb') as f:
            file_bytes = np.asarray(bytearray(f.read()), dtype=np.uint8)
        template = cv2.imdecode(file_bytes, cv2.IMREAD_COLOR)
        if template is None:
            raise ValueError(f"【{step_name}】，无法加载模板图像：{template_path}")
    
        # 执行模板匹配
        result = cv2.matchTemplate(screenshot, template, cv2.TM_CCOEFF_NORMED)
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(result)
    
        # 如果相似度超过阈值
        if max_val >= similarity_threshold:
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

                            # 计算点击或滚动的参考位置
                            if is_dynamic == "1":
                                x = max_loc[0] + template.shape[1] // 2
                                y = max_loc[1] + template.shape[0] // 2
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
                new_keyboard_input = entry.get()
                self.image_list[selected_index] = (
                    selected_image[0], selected_image[1], selected_image[2],
                    new_keyboard_input, selected_image[4], selected_image[5],
                    selected_image[6], selected_image[7], selected_image[8], selected_image[9], selected_image[10],
                    selected_image[11], selected_image[12], selected_image[13],
                )
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
                self.image_list[selected_index] = (
                    selected_image[0], selected_image[1], selected_image[2],
                    selected_image[3], mouse_action, selected_image[5],
                    selected_image[6], selected_image[7], selected_image[8], selected_image[9], mouse_action_result, selected_image[11],
                    selected_image[12], selected_image[13]
                )
                
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
        dialog.title("偏移坐标")
        dialog.transient(self.root)
        dialog.grab_set()

        # 创建输入框
        input_frame = tk.Frame(dialog)
        input_frame.pack(pady=10)

        tk.Label(input_frame, text="X 偏移量:").grid(row=0, column=0, padx=5, pady=5, sticky='e')
        x_entry = tk.Entry(input_frame, width=10)
        x_entry.insert(0, "0")  # 默认值0
        x_entry.grid(row=0, column=1, padx=5, pady=5)

        tk.Label(input_frame, text="Y 偏移量:").grid(row=1, column=0, padx=5, pady=5, sticky='e')
        y_entry = tk.Entry(input_frame, width=10)
        y_entry.insert(0, "0")  # 默认值0
        y_entry.grid(row=1, column=1, padx=5, pady=5)

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
        dialog.title("选择配置文件")
        dialog.transient(self.root)
        dialog.grab_set()

        # 主容器框架
        main_frame = tk.Frame(dialog)
        main_frame.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)

        # 列表框标题
        tk.Label(main_frame, text="请选择要加载的配置文件:").pack(anchor=tk.W)

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

        for config_file in config_files:
            # 如果这个配置文件是当前已加载的，添加后缀
            display_name = config_file
            if current_loaded and config_file == current_loaded:
                display_name = f"{config_file} (当前配置)"
            listbox.insert(tk.END, display_name)

        # 使用grid布局让列表框和滚动条并排
        listbox.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")

        # 配置grid权重
        list_container.grid_rowconfigure(0, weight=1)
        list_container.grid_columnconfigure(0, weight=1)

        # 创建右键菜单
        context_menu = tk.Menu(dialog, tearoff=0)
        context_menu.add_command(label="删除配置", command=lambda: self.delete_config(dialog, listbox, working_dir))
        
        #打开文件位置
        def open_file_location():
            if listbox.curselection():
                selected_index = listbox.curselection()[0]
                selected_file = config_files[selected_index]
                file_path = os.path.join(working_dir, selected_file)
                subprocess.Popen(f'explorer /select,"{file_path}"', 
                                creationflags=subprocess.CREATE_NO_WINDOW)
        
        context_menu.add_command(label="打开文件位置", command=open_file_location)
        
        # 绑定右键事件
        def show_context_menu(event):
            if listbox.curselection():
                context_menu.post(event.x_root, event.y_root)
                
        listbox.bind("<Button-3>", show_context_menu)

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
        dialog.geometry(f"{new_w}x{new_h}+{x}+{y}")
        dialog.deiconify()

        dialog.iconbitmap("icon/app.ico")
        
        dialog.protocol("WM_DELETE_WINDOW", on_cancel)
        self.root.wait_window(dialog)
        self.load_selected_config()

    def load_selected_config(self):
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
                # 确保每个项目都有 14 个元素
                if len(img_data) < 14:
                    img_data += [""] * (14 - len(img_data))
                    self.image_list[i] = img_data  # 更新原列表中的内容

                # 加载图像并创建缩略图
                try:
                    image = Image.open(img_data[0])
                    image.thumbnail((50, 50))
                    photo = ImageTk.PhotoImage(image)

                    # 插入到 Treeview
                    tree_item = self.tree.insert("", tk.END, values=(
                        os.path.basename(img_data[0]),  # 图片名称
                        img_data[1],  # 步骤名称
                        img_data[2],  # 相似度
                        img_data[3],  # 键盘动作
                        img_data[4],  # 坐标(F2)
                        img_data[5],  # 延时ms
                        img_data[6],  # 条件
                        img_data[7],  # 需跳转
                        img_data[8],  # 状态
                        img_data[9],  # 需禁用
                        img_data[10], # 鼠标动作
                        img_data[11], # 条件2
                        img_data[12], # 需跳转2
                        img_data[13], # 需禁用2
                    ), image=photo)
                    self.tree.image_refs.append(photo)
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
            
            print(f"配置已从 {self.config_filename} 加载")
            logging.info(f"配置已从 {self.config_filename} 加载")
            
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
            export_window.title("选择导出的配置文件")
            export_window.transient(self.root)
            export_window.grab_set()

            # 主容器框架
            main_frame = tk.Frame(export_window)
            main_frame.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)

            # 列表框标题
            tk.Label(main_frame, text="请选择要导出的配置文件:").pack(anchor=tk.W)

            # 列表框容器
            list_container = tk.Frame(main_frame)
            list_container.pack(fill=tk.BOTH, expand=True)

            # 列表框和滚动条
            listbox = tk.Listbox(list_container, selectmode=tk.SINGLE)
            scrollbar = tk.Scrollbar(list_container)

            scrollbar.config(command=listbox.yview)
            listbox.config(yscrollcommand=scrollbar.set)

            for file in config_files:
                listbox.insert(tk.END, file)

            # 使用grid布局让列表框和滚动条并排
            listbox.grid(row=0, column=0, sticky="nsew")
            scrollbar.grid(row=0, column=1, sticky="ns")

            # 配置grid权重
            list_container.grid_rowconfigure(0, weight=1)
            list_container.grid_columnconfigure(0, weight=1)

            # 创建右键菜单
            context_menu = tk.Menu(export_window, tearoff=0)
            context_menu.add_command(label="删除配置", command=lambda: self.delete_config(export_window, listbox, working_dir))

            #打开文件位置
            def open_file_location():
                if listbox.curselection():
                    selected_index = listbox.curselection()[0]
                    selected_file = config_files[selected_index]
                    file_path = os.path.join(working_dir, selected_file)
                    os.system(f'explorer /select,"{file_path}"')
            
            context_menu.add_command(label="打开文件位置", command=open_file_location)
            
            # 绑定右键事件
            def show_context_menu(event):
                if listbox.curselection():
                    context_menu.post(event.x_root, event.y_root)
                    
            listbox.bind("<Button-3>", show_context_menu)

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
            
            self.image_list[selected_index] = (
                selected_image[0], selected_image[1], selected_image[2], 
                selected_image[3], mouse_action, selected_image[5], 
                selected_image[6], selected_image[7], selected_image[8], selected_image[9], selected_image[10],
                selected_image[11], selected_image[12], selected_image[13], 
            )

            step_name = selected_image[1]
            old_coodr = selected_image[4].split(":")[1] if selected_image[4] and ":" in selected_image[4] else selected_image[4]
            new_coodr = x, y
            logging.info(f"【{step_name}】坐标更新：({old_coodr}) → {new_coodr}")      
            print(f"【{step_name}】坐标更新：({old_coodr}) → {new_coodr}")
            
            self.update_image_listbox()
            messagebox.showinfo("更新坐标", f"坐标已更新为({x}, {y})")
   
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
        self.context_menu.add_command(label="重新截图", command=self.retake_screenshot)
        self.context_menu.add_command(label="关闭识图", command=self.Image_recognition_click)  # 默认显示为“关闭识图”，索引1
        self.context_menu.add_command(label="条件跳转", command=self.set_condition_jump)
        self.context_menu.add_separator() #索引3
        self.context_menu.add_command(label="复制", command=self.copy_item)
        self.context_menu.add_command(label="剪切", command=self.cut_item)
        self.context_menu.add_command(label="粘贴", command=self.paste_item)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="删除", command=self.delete_selected_image)
        self.context_menu.add_command(label="禁用", command=self.toggle_disable_status)  # 注意保持为“禁用”，索引9
        self.context_menu.add_separator()
        self.context_menu.add_command(label="从此步骤运行", command=self.start_from_step)
        self.context_menu.add_command(label="打开图片位置", command=self.open_image_location)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="重命名", command=self.edit_image_name)
        self.context_menu.add_command(label="延时ms", command=self.edit_wait_time)
        self.context_menu.add_command(label="相似度", command=self.edit_similarity_threshold)
        self.context_menu.add_command(label="键盘动作", command=self.edit_keyboard_input)
        self.context_menu.add_command(label="鼠标动作", command=self.edit_mouse_action)
        self.context_menu.add_command(label="偏移坐标", command=self.offset_coords)
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
            self.context_menu.entryconfig(9, label=new_disable_label, command=self.toggle_disable_status)
            self.update_label() # 更新详细信息
    
    def toggle_disable_status(self):
        selected = self.tree.selection()
        if selected:
            selected_item = selected[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]  # 获取原始数据

            # 切换状态（索引8），保持其他字段不变，且【需禁用】（索引9）不变
            new_status = "禁用" if selected_image[8] != "禁用" else "启用"
            
            # 创建新的元组
            updated_image = (
                selected_image[0],  # 图片路径
                selected_image[1],  # 步骤名称
                selected_image[2],  # 相似度阈值
                selected_image[3],  # 键盘动作
                selected_image[4],  # 鼠标点击坐标
                selected_image[5],  # 等待时间
                selected_image[6],  # 条件
                selected_image[7],  # 需跳转
                new_status,         # 更新状态
                selected_image[9], # 【需禁用】目标
                selected_image[10], #鼠标动作
                selected_image[11],  # 条件2
                selected_image[12],  # 需跳转2
                selected_image[13],  # 需禁用2
            )

            # 更新数据源
            self.image_list[selected_index] = updated_image

            # 更新 TreeView 项（确保显示10个字段，文件名只显示 basename）
            self.tree.item(selected_item, values=(
                os.path.basename(updated_image[0]), 
                updated_image[1],
                updated_image[2],
                updated_image[3],
                updated_image[4],
                updated_image[5],
                updated_image[6],
                updated_image[7],
                updated_image[8],
                updated_image[9],
                updated_image[10],
                updated_image[11],
                updated_image[12],
                updated_image[13],
            ))
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
            messagebox.showinfo("提示", "请先点击【停止运行】")

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

    def copy_item(self):
        if self.is_cut_mode:
            self.restore_cut()
            messagebox.showinfo("提示","已恢复剪切后未粘贴的步骤，请重新复制")
            return
        selected = self.tree.selection()
        if not selected:
            return
        # 普通复制，不触发剪切模式
        self.is_cut_mode = False
        self.cut_original_indices = []
        self.copied_items = []
        for sel in selected:
            idx = self.tree.index(sel)
            original = self.image_list[idx]
            new_path = self.create_image_copy(original[0])
            record = [new_path] + list(original[1:])
            self.copied_items.append(record)

        print(f"已复制 {len(self.copied_items)} 个项目")
        self.tree.selection_clear()
        # —— 强制清除所有选中和焦点 —— 
        self.tree.selection_remove(self.tree.selection())

    def create_image_copy(self, original_path):
        """
        在原文件同目录下复制一份图像文件。
        逻辑：
        - 如果文件名末尾形如 base_数字，则提取 base 作为基础名；
        - 否则完整保留原始文件名作为基础名；
        - 然后从 _1 开始尝试（base_1.ext），若已存在则依次 base_2.ext、base_3.ext ... 直到不冲突。
        返回新文件的完整路径。
        """
        dirname = os.path.dirname(original_path)
        base_name = os.path.basename(original_path)
        name, ext = os.path.splitext(base_name)

        # 仅当文件名末尾有下划线加数字时，提取出基础名
        # 例如 name_3 -> group(1)=name；否则（如 "20250611184011" 或 "image"）都保持原 name
        m = re.match(r"^(.*)_(\d+)$", name)
        if m:
            base = m.group(1)
        else:
            base = name

        # 从 1 开始尝试 _1 后缀
        count = 1
        new_name = f"{base}_{count}{ext}"
        new_path = os.path.join(dirname, new_name)
        while os.path.exists(new_path):
            count += 1
            new_name = f"{base}_{count}{ext}"
            new_path = os.path.join(dirname, new_name)

        shutil.copy2(original_path, new_path)
        return new_path
       
    def cut_item(self):
        selected = self.tree.selection()
        if not selected:
            messagebox.showinfo("提示", "请先选择要剪切的项目")
            return

        self.is_cut_mode = True

        # 收集索引并降序删除
        indices = sorted((self.tree.index(iid) for iid in selected), reverse=True)
        for idx in indices:
            self.cut_original_indices.append(idx)
            self.copied_items.append(self.image_list.pop(idx))

        # 刷新界面
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

        # 处理粘贴的文件名（避免重复）
        new_records = []
        for record in self.copied_items:
            original_path = record[0]
            dirname = os.path.dirname(original_path)
            base_name = os.path.basename(original_path)
            name, ext = os.path.splitext(base_name)

            # 如果文件名已经包含 _数字 后缀，则提取原始名称
            import re
            match = re.match(r"^(.*?)(_\d+)?$", name)
            if match:
                name = match.group(1)  # 只保留原始名称部分

            # 检查目标路径是否已存在
            new_name = f"{name}{ext}"
            new_path = os.path.join(dirname, new_name)

            # 如果已存在，则添加 _1, _2, ... 后缀
            count = 1
            while os.path.exists(new_path):
                new_name = f"{name}_{count}{ext}"
                new_path = os.path.join(dirname, new_name)
                count += 1

            # 复制文件（如果是剪切模式则移动文件）
            if self.is_cut_mode:
                os.rename(original_path, new_path)
            else:
                shutil.copy2(original_path, new_path)

            # 更新记录
            new_record = [new_path] + list(record[1:])
            new_records.append(new_record)

        # 插入到 data list
        for i, record in enumerate(new_records):
            self.image_list.insert(insert_pos + i, record)

        # 刷新界面并聚焦新行
        self.update_image_listbox()
        new_iids = self.tree.get_children()[insert_pos: insert_pos + len(new_records)]
        if new_iids:
            self.tree.selection_set(new_iids)
            self.tree.focus(new_iids[0])
            self.tree.see(new_iids[-1])

        if self.is_cut_mode:
            self.cut_original_indices.clear()
            self.copied_items.clear()

        # 退出剪切模式
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
                selected_image[0],
                selected_image[1],
                new_similarity,
                selected_image[3],
                selected_image[4],
                selected_image[5],
                selected_image[6],
                selected_image[7],
                selected_image[8],
                selected_image[9],
                selected_image[10],
                selected_image[11],
                selected_image[12],
                selected_image[13]
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

    def edit_wait_time(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]
   
            dialog = tk.Toplevel(self.root)
            dialog.withdraw()                     # 先隐藏
            dialog.title("修改延时ms")
            dialog.transient(self.root)
            dialog.grab_set()

            # 标签和输入框
            label = tk.Label(dialog, text="请输入新的延时（毫秒）")
            label.pack(padx=10, pady=10)
            entry = tk.Entry(dialog)
            entry.pack(padx=10, pady=5)
            entry.insert(0, str(selected_image[5]))

            # 保存和取消按钮
            button_frame = tk.Frame(dialog)
            button_frame.pack(pady=10)

            def on_save():
                try:
                    new_wait_time = int(entry.get())
                except ValueError:
                    messagebox.showerror("错误", "请输入有效的整数。", parent=dialog)
                    return

                self.image_list[selected_index] = (
                    selected_image[0],
                    selected_image[1],
                    selected_image[2],
                    selected_image[3],
                    selected_image[4],
                    new_wait_time,
                    selected_image[6],
                    selected_image[7],
                    selected_image[8],
                    selected_image[9],
                    selected_image[10],
                    selected_image[11],
                    selected_image[12],
                    selected_image[13],
                )
                self.update_image_listbox()
                dialog.destroy()

            # 在创建按钮时添加bootstyle参数
            save_button = ttk.Button(
                button_frame, 
                text="保存", 
                command=on_save,
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
                selected_image[3],  # 其他字段保持不变
                selected_image[4],
                selected_image[5],
                selected_image[6],
                selected_image[7],
                selected_image[8],
                selected_image[9],
                selected_image[10],
                selected_image[11],
                selected_image[12],
                selected_image[13],
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
            # 更新 selected_image 中的相似度（修正索引错误）
            self.image_list[selected_index] = (
                selected_image[0],  # 图片路径（索引 0）
                selected_image[1],  # 步骤名称（索引 1）
                new_similarity_threshold,  # 新的相似度（索引 2）
                selected_image[3],  # 键盘动作（索引 3）
                selected_image[4],  # 坐标（索引 4）
                selected_image[5],  # 延时ms（索引 5）
                selected_image[6],  # 条件（索引 6，之前遗漏导致后续字段错位）
                selected_image[7],  # 需跳转（索引 7）
                selected_image[8],  # 状态（索引 8，必须保留）
                selected_image[9],   # 需禁用（索引 9，必须保留）
                selected_image[10], #鼠标动作
                selected_image[11],  # 条件2
                selected_image[12],   # 需跳转2
                selected_image[13], #需禁用2
            )
            
            # 更新界面显示
            self.update_image_listbox()
    
    def edit_image_name(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]

            dialog = tk.Toplevel(self.root)
            dialog.withdraw()                     # 先隐藏
            dialog.title("重命名")
            dialog.transient(self.root)
            dialog.grab_set()

            # 标签和输入框
            label = tk.Label(dialog, text="请输入新的步骤名称")
            label.pack(padx=10, pady=10)
            entry = tk.Entry(dialog)
            entry.pack(padx=10, pady=5)
            entry.insert(0, selected_image[1])

            # 保存和取消按钮
            button_frame = tk.Frame(dialog)
            button_frame.pack(pady=10)

            def on_save():
                new_image_name = entry.get()
                self.image_list[selected_index] = (
                    selected_image[0],
                    new_image_name,
                    selected_image[2],
                    selected_image[3],
                    selected_image[4],
                    selected_image[5],
                    selected_image[6],
                    selected_image[7],
                    selected_image[8],
                    selected_image[9],
                    selected_image[10],
                    selected_image[11],
                    selected_image[12],
                    selected_image[13],
                )
                self.update_image_listbox()
                dialog.destroy()
                
            # 在创建按钮时添加bootstyle参数
            save_button = ttk.Button(
                button_frame, 
                text="保存", 
                command=on_save,
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

            # 默认选中所有文本
            entry.select_range(0, tk.END)  # 选中所有文本
            entry.icursor(tk.END)         # 将光标放在末尾（可选）
            entry.focus_set()             # 确保输入框获得焦点

            dialog.iconbitmap("icon/app.ico")
   
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
        dialog.title("条件跳转")
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

        # 取出现有的两个跳转值
        current_jump1 = selected_image[7] if len(selected_image) > 7 else ""
        current_jump2 = selected_image[12] if len(selected_image) > 12 else ""
        jump_var1 = tk.StringVar(value="无" if not current_jump1 else current_jump1)
        jump_var2 = tk.StringVar(value="无" if not current_jump2 else current_jump2)

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

            # 验证逻辑：只要存在任意跳转或禁用，就必须填写条件
            if (jump1 or dis1) and not (cond1):
                messagebox.showwarning(
                    "警告", 
                    "请指定条件1！", 
                    parent=dialog
                )
                return
            
            if (jump2 or dis2) and not (cond2):
                messagebox.showwarning(
                    "警告", 
                    "请指定条件2！", 
                    parent=dialog
                )
                return

            try:
                # 确保 selected_image 列表长度至少为 14（索引 0 到 13）
                while len(selected_image) < 14:
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
            # 加载默认图像
            self.load_default_image()
            self.clear_labels()
            return
        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
          
        try:
            # 获取选中项的图像路径
            img_path = self.image_list[selected_index][0]
            
            # 加载图像
            original_image = Image.open(img_path)
            original_width, original_height = original_image.size

            # 通过主窗口获取分辨率
            root_window = self.root 
            screen_width = root_window.winfo_screenwidth()
            screen_height = root_window.winfo_screenheight()

            # 动态设置预览尺寸
            if screen_width >= 2560 and screen_height >= 1440:
                max_size = (279, 217)
            else:
                max_size = (290, 220)
            
            # 保持原有缩放逻辑
            width_ratio = max_size[0] / original_width
            height_ratio = max_size[1] / original_height
            scale_ratio = min(width_ratio, height_ratio)
            
            new_size = (
                int(original_width * scale_ratio),
                int(original_height * scale_ratio)
            )
            
            resized_image = original_image.resize(new_size, Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized_image)
            
            self.preview_image_label.config(image=photo)
            self.preview_image_label.image = photo
            self.update_label()
              
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
            font=('Consolas', 10)
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