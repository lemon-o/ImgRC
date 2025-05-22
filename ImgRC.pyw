# -*- coding: utf-8 -*-
from pathlib import Path
import subprocess
import tempfile
import tkinter as tk
from tkinter import filedialog, ttk, messagebox
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
        # 设置窗口居中显示
        self.center_window()
        # 设置窗口图标（相对路径）
        root.iconbitmap("icon/app.ico")   
        # 获取屏幕高度
        screen_height = root.winfo_screenheight()    
        # 根据屏幕高度设置窗口尺寸
        if 1080 <= screen_height < 1440:  # 普通高清屏(1080p)
            self.root.geometry("620x600")
        elif 1440 <= screen_height < 2160:  # 2K屏
            self.root.geometry("650x635")
        else:  # 其他分辨率使用默认尺寸
            self.root.geometry("620x600")  
        self.root.resizable(False, False)  # 禁止调整窗口大小
        self.style = tb.Style(theme='flatly')  # 选择一个主题
        self.image_list = []  # 存储 (图像路径, 步骤名称, 相似度, 键盘动作, 坐标(F2), 延时ms, 条件, 需跳转，状态， 需禁用， 鼠标动作)
        self.screenshot_area = None  # 用于存储截图区域
        self.rect = None  # 用于存储 Canvas 上的矩形
        self.start_x = None
        self.start_y = None
        self.canvas = None
        self.running = False  # 控制脚本是否在运行
        self.thread = None  # 用于保存线程
        self.hotkey = '<F9>'  # 默认热键
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
        self.screen_scale = 1
        self.follow_current_step = tk.BooleanVar(value=False)  # 控制是否跟随当前步骤
        self.only_keyboard_var = tk.BooleanVar(value=False)  # 控制是否只进行键盘操作
        self.init_ui()
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
        self.region_a = tb.Frame(self.region_l)
        self.region_a.pack(fill=tk.X, padx=2, pady=5)

        # 图标缓存
        self.icons = {
            "export": load_icon("export.png"),
            "import": load_icon("import.png"),
            "save": load_icon("save.png"),
            "load": load_icon("load.png")
        }

        self.hover_icons = {
            "export": load_icon("export_hover.png"),
            "import": load_icon("import_hover.png"),
            "save": load_icon("save_hover.png"),
            "load": load_icon("load_hover.png")
        }

        # 用于放置按钮的框架，设置为水平排列
        self.config_button_frame = ttk.Frame(self.region_a)
        self.config_button_frame.pack(pady=5)

        # 定义鼠标进入和离开的回调函数
        def on_enter(event, button, hover_icon):
            button.config(image=hover_icon)

        def on_leave(event, button, normal_icon):
            button.config(image=normal_icon)

        # 导出配置按钮
        self.Export_config_button = ttk.Button(
            self.config_button_frame, image=self.icons["export"],
            command=self.export_config, bootstyle="primary-outline"
        )
        self.Export_config_button.pack(side=tk.LEFT, padx=5)
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
            self.config_button_frame, image=self.icons["import"],
            command=self.import_config, bootstyle="primary-outline"
        )
        self.Import_config_button.pack(side=tk.LEFT, padx=5)
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
            self.config_button_frame, image=self.icons["save"],
            command=self.save_config, bootstyle="primary-outline"
        )
        self.save_config_button.pack(side=tk.LEFT, padx=5)
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
            self.config_button_frame, image=self.icons["load"],
            command=self.load_config, bootstyle="primary-outline"
        )
        self.load_config_button.pack(side=tk.LEFT, padx=5)
        ToolTip(self.load_config_button, "加载配置")
        self.load_config_button.bind(
            "<Enter>", 
            lambda e: on_enter(e, self.load_config_button, self.hover_icons["load"]), add="+"  
        )
        self.load_config_button.bind(
            "<Leave>", 
            lambda e: on_leave(e, self.load_config_button, self.icons["load"]), add="+"  
        )

        # 用于放置【截取图片】和【删除图片】
        self.top_button_frame = tb.Frame(self.region_a)
        self.top_button_frame.pack(pady=10)

        # 截取图片按钮
        self.screenshot_button = tb.Button(self.top_button_frame, text="截取图片", command=self.prepare_capture_screenshot, bootstyle="primary-outline")
        self.screenshot_button.pack(side=tk.LEFT, padx=5)

        # 运行/停止脚本按钮
        self.toggle_run_button = tb.Button(self.top_button_frame, text="开始运行(F9)", command=self.toggle_script, bootstyle="primary-outline")
        self.toggle_run_button.pack(side=tk.LEFT, padx=5)

        # 循环次数输入框
        self.loop_count_frame = tb.Frame(self.region_a)
        self.loop_count_frame.pack(pady=5)

        self.loop_count_label = tb.Label(self.loop_count_frame, text="循环次数:")
        self.loop_count_label.pack(side=tk.LEFT, padx=5)
        self.loop_count_entry = tb.Entry(self.loop_count_frame)
        self.loop_count_entry.insert(0, str(self.loop_count))
        self.loop_count_entry.pack(side=tk.LEFT, padx=5)

        # 区域M：勾选框区域
        self.region_m = tb.Frame(self.region_l)
        self.region_m.pack(fill=tk.X, padx=2, pady=2)

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
        self.allow_minimize_checkbox.pack(side=tk.LEFT, pady=5)

        # 窗口置顶
        self.follow_step_checkbox = tb.Checkbutton(
            self.region_m, 
            text="窗口置顶", 
            variable=self.follow_current_step, 
            bootstyle="toolbutton",
            command=self.toggle_topmost
        )
        self.follow_step_checkbox.pack(side=tk.LEFT, pady=5)


        # 仅键盘操作勾选框
        self.only_keyboard_checkbox = tb.Checkbutton(self.region_m, text="仅键盘操作", variable=self.only_keyboard_var, bootstyle=TOOLBUTTON)
        self.only_keyboard_checkbox.pack(side=tk.LEFT, pady=5)

        # 区域B：树形区域
        self.region_b = tb.Frame(self.region_l)
        self.region_b.pack(fill=tk.BOTH, expand=True, padx=2, pady=5)

        # 使用 Treeview 来显示图片和延时ms
        self.tree = ttk.Treeview(self.region_b, columns=(
            "图片名称", "步骤名称", "相似度", "键盘动作", "坐标(F2)", "延时ms", "条件", "需跳转", "状态", "需禁用", "鼠标动作"
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
        self.region_r_border.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=7, pady=15)

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

        # 预览面板（精确高度控制）
        self.preview_panel = tb.Frame(
            self.region_c,
            width=357,
            height=236
        )
        self.preview_panel.pack_propagate(False)
        self.preview_panel.pack()  

        # 图像容器（精确高度控制）
        self.preview_container = tb.Frame(
            self.preview_panel,
            width=340,
            height=240,
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
        self.region_d.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))  # 关键修改

        # 详细信息标签区域（保持原样）
        self.label_frame = tk.Frame(self.region_d, width=350)
        self.label_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=10)
        self.label_frame.pack_propagate(False)

        # 标题标签
        self.label_title = tk.Label(
            self.label_frame,
            text="详细信息",
            anchor="w",
            font=('Arial', 10, 'bold'),
            foreground="#3b3b3b"
        )
        self.label_title.pack(fill="x", padx=5, pady=7)

        # 详细信息标签
        self.labels = {
            "图片名称": tk.Label(self.label_frame, text="图片名称: ", anchor="w"),
            "相似度": tk.Label(self.label_frame, text="相似度: ", anchor="w"),
            "坐标(F2)": tk.Label(self.label_frame, text="坐标(F2): ", anchor="w"),
            "键盘动作": tk.Label(self.label_frame, text="键盘动作: ", anchor="w"),
            "鼠标动作": tk.Label(self.label_frame, text="鼠标动作: ", anchor="w"),
            "状态": tk.Label(self.label_frame, text="状态: ", anchor="w"),
            "条件": tk.Label(self.label_frame, text="条件: ", anchor="w"),
            "需跳转": tk.Label(self.label_frame, text="需跳转: ", anchor="w"),
            "需禁用": tk.Label(self.label_frame, text="需禁用: ", anchor="w"),
        }
        for lbl in self.labels.values():
            lbl.configure(foreground="#495057")
            lbl.pack(fill="x", padx=5, pady=2)
            
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

    def center_window(self):
        """
        将窗口居中显示
        """
        # 获取屏幕宽度和高度
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()

        # 设置窗口的宽度和高度
        window_width = 657  # 你可以根据需要调整窗口宽度
        window_height = 543  # 你可以根据需要调整窗口高度

        # 计算窗口居中的位置
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2

        # 设置窗口的位置和大小
        self.root.geometry(f"{window_width}x{window_height}+{x}+{y}")
        
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

    def on_treeview_drag_start(self, event):
        """开始拖动时记录选中的行"""
        item = self.tree.identify_row(event.y)
        if item:
            self.dragged_item = item

    def on_treeview_drag_motion(self, event):
        """鼠标拖动时高亮目标位置"""
        if not hasattr(self, "dragged_item"):
            return

        target_item = self.tree.identify_row(event.y)
        if target_item and target_item != self.dragged_item:
            self.tree.selection_set(target_item)  # 选中目标行

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

        # 字段配置 (名称: 索引)
        字段配置 = {
            "图片名称": 0, "相似度": 2, "坐标(F2)": 4,
            "键盘动作": 3, "鼠标动作": 10, "状态": 8,
            "条件": 6, "需跳转": 7, "需禁用": 9
        }

        for 字段名, 索引 in 字段配置.items():
            raw = str(values[索引]).replace("\n", " ").strip()
            disp = 截断文本(raw)
            lbl = self.labels[字段名]

            # 取消所有旧绑定，并更新文本
            lbl.unbind("<Enter>")
            lbl.unbind("<Leave>")
            lbl.config(text=f"{字段名}:  {disp}",
                       wraplength=0)
            lbl.grid(sticky="ew")

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
        """清空 Label 内容，仅保留标题"""
        for key in self.labels:
            self.labels[key].config(text=f"{key}: ")

    def register_global_hotkey(self):
        try:
            def hotkey_callback():
                self.root.after(0, self.toggle_script)  # 使用 after 在主线程中调用
             
            # 解析热键字符串
            hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
            keyboard.add_hotkey(hotkey_str, hotkey_callback)
            
            print(f"-------------------------------------------------------------------------------------")
            logging.info(f"-------------------------------------------------------------------------------------")             
            print(f"全局热键已注册：{self.hotkey}")
            logging.info(f"程序启动")
        except Exception as e:
            print(f"注册热键失败: {e}")
 
    def unregister_global_hotkey(self):
        try:
           hotkey_str = self.hotkey.replace('<', '').replace('>', '').lower()
           keyboard.remove_hotkey(hotkey_str)
           print(f"全局热键已注销：{self.hotkey}")
        except Exception as e:
           print(f"注销全局热键出错：{e}")
 
    def prepare_capture_screenshot(self):
        # 捕获全屏快照
        screenshot = ImageGrab.grab()  # 全屏捕获
        self.full_screen_image = screenshot  # 保存原始快照，后续用于局部处理
        self.screenshot_photo = ImageTk.PhotoImage(screenshot)
        # 计算新的步骤编号
        existing_steps = set()
        for item in self.image_list:
            step_name = item[1]
            if step_name.startswith("步骤"):
                try:
                    num = int(step_name[2:])  # 提取"步骤"后面的数字
                    existing_steps.add(num)
                except ValueError:
                    continue
        new_step_num = 1
        while new_step_num in existing_steps:
            new_step_num += 1
        self._next_step_num = new_step_num

        # 创建一个全屏窗口用于显示快照
        self.top = tk.Toplevel(self.root)
        self.top.attributes('-fullscreen', True)
        self.top.focus_force()  # 确保窗口获取焦点
        self.top.bind("<Escape>", self.exit_screenshot_mode)
        print("Esc 绑定成功")  # Debug 信息

        # 在窗口上创建 Canvas，并在 Canvas 中显示快照图片
        self.canvas = tk.Canvas(self.top, cursor="cross")
        self.canvas.pack(fill=tk.BOTH, expand=True)
        # 保存创建的图像项标识符，用于后续更新显示
        self.image_id = self.canvas.create_image(0, 0, anchor=tk.NW, image=self.screenshot_photo)

        # 初始化鼠标拖动相关的属性
        self.rect = None
        self.overlay_rects = []
        
        # 绑定鼠标事件，用于在快照上选择区域
        self.canvas.bind("<ButtonPress-1>", self.on_button_press)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_button_release)
                
    def exit_screenshot_mode(self, event=None):
        """退出截图模式，关闭透明窗口，恢复主窗口"""
        if hasattr(self, 'top') and self.top:  # 确保 self.top 存在
            self.top.destroy()
            self.top = None  # 释放引用，防止重复调用时报错
        self.root.deiconify()  # 重新显示主窗口
   
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
        end_x = event.x
        end_y = event.y

        # 删除覆盖层，释放画布
        for item in self.overlay_rects:
            self.canvas.delete(item)
        self.overlay_rects = []

        # 获取截图区域，不包括矩形框
        border_offset = 2  # 让截图区域比矩形框内缩 2 像素
        bbox = (
            min(self.start_x, end_x) + border_offset, 
            min(self.start_y, end_y) + border_offset, 
            max(self.start_x, end_x) - border_offset, 
            max(self.start_y, end_y) - border_offset
        )
            
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
                    selected_image[10]      # 10: 鼠标动作
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
                self.image_list.insert(insert_index, (screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次"))
            else:
                self.image_list.append((screenshot_path, step_name, 0.8, "", mouse_click_coordinates, 100, "", "", "启用", "", "左键单击 1次"))

        self.update_image_listbox()  # 更新详细信息

        # 关闭全屏透明窗口
        self.top.destroy()
        self.root.deiconify()

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
                    while len(full_item) < 11:
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
                        mouse_action_result
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
                            mouse_action_result
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
            print("已更新配置文件:", self.config_filename)
            logging.info("已更新配置文件: %s", self.config_filename)

    def delete_selected_image(self):
        try:
            selected_item = self.tree.selection()
            if not selected_item:
                messagebox.showinfo("提示", "请先选择要删除的项目")
                return
   
            selected_index = self.tree.index(selected_item[0])
            if 0 <= selected_index < len(self.image_list):
                selected_image = self.image_list[selected_index]
                img_path = selected_image[0]
                   
                if messagebox.askyesno("确认删除", "是否删除该步骤和对应的图片文件？"):
                    del self.image_list[selected_index]
                    # 检查是否有其他项目引用相同的图像文件
                    is_referenced = any(item[0] == img_path for item in self.image_list)
                    if not is_referenced and os.path.exists(img_path):
                        try:
                            os.remove(img_path)
                            print(f"图像文件已删除: {img_path}")
                            logging.info(f"图像文件已删除: {img_path}")
                        except Exception as e:
                            print(f"删除图像文件时出错: {e}")
                            logging.error(f"删除图像文件时出错: {e}")
                   
                self.update_image_listbox()
                self.load_default_image()
                self.clear_labels()

            else:
                print("选中的索引超出范围")
                logging.warning("选中的索引超出范围")
        except Exception as e:
            print(f"删除图像时出错: {e}")
            logging.error(f"删除图像时出错: {e}")
   
    def toggle_script(self, event=None):
        if self.toggle_run_button.cget("text") == "停止运行(F9)":
            self.stop_script()
            return
        
        if not self.running:
            if not self.image_list:
                messagebox.showwarning("提示", "列表中无步骤，【截取图片】【加载步骤】【导入步骤】可添加步骤")
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
                # 注意：disable_target 与跳转无关，单独判断；假设存储在索引 9
                disable_target = current_step[9] if len(current_step) > 9 else ""

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

                # -------------------------------
                # 单独处理【需禁用】目标步骤（与跳转无关）
                if disable_target:
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
                        print(f"需禁用的目标 {disable_target} 不存在")
                # -------------------------------
                # 分离处理需跳转
                if condition and jump_to:
                    should_jump = False
                    if condition == "识图成功" and match_result:
                        should_jump = True
                        print(f"【{img_name}】执行完毕")
                        logging.info(f"【{img_name}】执行完毕")
                        print(f"从【{img_name}】跳转到【{jump_to}】")
                        logging.info(f"从【{img_name}】跳转到【{jump_to}】")
                    elif condition == "识图失败" and not match_result:
                        should_jump = True
                        print(f"【{img_name}】执行完毕")
                        logging.info(f"【{img_name}】执行完毕")
                        print(f"从【{img_name}】跳转到【{jump_to}】")
                        logging.info(f"从【{img_name}】跳转到【{jump_to}】")

                    if should_jump:
                        if jump_to in self.step_index_map:
                            index = self.step_index_map[jump_to]
                            continue
                        else:
                            print(f"跳转目标 {jump_to} 不存在，停止执行")
                            self.running = False
                            break

                # 如果没有跳转且匹配失败，则尝试重试（仅适用于非键盘操作情况）
                if not match_result and not (condition and jump_to) and not self.only_keyboard_var.get():
                    match_result = self.retry_until_match(img_path, similarity_threshold, wait_time)

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
        # 收集所有被引用为 disable_target 的步骤名称
        disable_targets = set()
        for step in self.image_list:
            if len(step) > 9 and step[9]:
                disable_targets.add(step[9])
        
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

                except Exception as e:
                    print(f"【{step_name}】，鼠标操作时出错: {e}")
                    logging.error(f"【{step_name}】，鼠标操作时出错: {e}")
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

            # 创建新窗口但不隐藏主窗口
            dialog = tk.Toplevel(self.root)
            dialog.title("修改键盘动作")
            
            # 获取屏幕分辨率
            screen_width = self.root.winfo_screenwidth()
            screen_height = self.root.winfo_screenheight()

            # 根据分辨率和缩放比例设置对话框尺寸
            self.get_screen_scale()
            if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
                # 1080p (1920x1080) 到小于 1440p 的情况
                if self.screen_scale == 1.25:  # 125% 缩放
                    dialog_width = 620
                    dialog_height = 535
                elif self.screen_scale == 1:
                    dialog_width = 542
                    dialog_height = 490
                else:
                    dialog_width = 300
                    dialog_height = 340
            elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
                # 1440p (2560x1440) 到小于 2160p (4K) 的情况
                if self.screen_scale == 1.25:  # 125% 缩放
                    dialog_width = 630
                    dialog_height = 530
                else:
                    dialog_width = 630
                    dialog_height = 530
            else:
                # 其他情况使用默认尺寸
                dialog_width = 630
                dialog_height = 530

            # 获取主窗口位置和尺寸
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            main_height = self.root.winfo_height()
            
            # 计算居中位置
            center_x = main_x + (main_width - dialog_width) // 2
            center_y = main_y + (main_height - dialog_height) // 2
            
            # 设置对话框位置和大小
            dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
            
            # 设置窗口关系
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
                    selected_image[6], selected_image[7], selected_image[8], selected_image[9], selected_image[10]
                )
                self.update_image_listbox()
                dialog.destroy()
            dialog.iconbitmap("icon/app.ico")  # 设置窗口图标
            
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
   
    def edit_mouse_action(self):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        # 创建对话框（先不显示内容）
        dialog = tk.Toplevel(self.root)
        dialog.title("设置鼠标操作")

        # 获取屏幕分辨率
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()

        # 根据分辨率和缩放比例设置对话框尺寸
        self.get_screen_scale()
        if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
            # 1080p (1920x1080) 到小于 1440p 的情况
            if self.screen_scale == 1.25:  # 125% 缩放
                dialog_width = 278
                dialog_height = 390
            elif self.screen_scale == 1:
                dialog_width = 300
                dialog_height = 340
            else:
                dialog_width = 300
                dialog_height = 340
        elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
            # 1440p (2560x1440) 到小于 2160p (4K) 的情况
            if self.screen_scale == 1.25:  # 125% 缩放
                dialog_width = 300
                dialog_height = 390
            else:
                dialog_width = 300
                dialog_height = 340
        else:
            # 其他情况使用默认尺寸
            dialog_width = 300
            dialog_height = 390

        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        
        # 设置初始几何位置
        dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
        
        # 设置窗口关系
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

        # 动态点击勾选框
        dynamic_var = tk.BooleanVar(value=current_dynamic)
        tk.Checkbutton(action_frame, text="动态点击", variable=dynamic_var).pack(anchor=tk.W)

        def save_mouse_action():
            try:
                # 获取坐标
                coords = coord_entry.get().strip()
                if not coords or "," not in coords:
                    messagebox.showerror("错误", "请输入有效的坐标 (x,y)", parent=dialog)
                    return

                try:
                    x, y = map(int, coords.split(","))
                except ValueError:
                    messagebox.showerror("错误", "坐标必须是整数", parent=dialog)
                    return

                action = action_var.get()
                dynamic = "1" if dynamic_var.get() else "0"

                # 获取次数或滚动行数
                if action == "click":
                    count_str = left_click_entry.get().strip() if left_click_entry else "1"
                elif action == "scrollUp":
                    count_str = scroll_up_entry.get().strip()
                elif action == "scrollDown":
                    count_str = scroll_down_entry.get().strip()
                else:
                    count_str = "1"

                try:
                    count_val = int(count_str)
                    if count_val < 1:
                        raise ValueError
                except ValueError:
                    messagebox.showerror("错误", "请输入有效的次数/行数（正整数）", parent=dialog)
                    return

                # 生成鼠标操作字符串
                if action in ["click", "scrollUp", "scrollDown"]:
                    mouse_action = f"{action}:{coords}:{dynamic}:{count_val}"
                else:
                    mouse_action = f"{action}:{coords}:{dynamic}"

                # 转换鼠标操作字符串为可读格式
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
                
                if action in ["click", "scrollUp", "scrollDown"]:
                    mouse_action_result = f"{action_desc} {count_val}{unit}{dynamic_desc}"
                else:
                    mouse_action_result = f"{action_desc}{dynamic_desc}"

                # 更新 image_list
                self.image_list[selected_index] = (
                    selected_image[0], selected_image[1], selected_image[2],
                    selected_image[3], mouse_action, selected_image[5],
                    selected_image[6], selected_image[7], selected_image[8], selected_image[9], mouse_action_result
                )
                
                self.update_image_listbox()
                dialog.destroy()

            except Exception as e:
                messagebox.showerror("错误", f"保存鼠标操作时出错: {str(e)}", parent=dialog)

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
        dialog.iconbitmap("icon/app.ico")  # 设置窗口图标

        # 最终调整窗口大小（如果需要）
        dialog.update_idletasks()
        dialog_width = dialog.winfo_width()
        dialog_height = dialog.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        dialog.geometry(f"+{center_x}+{center_y}")

    def offset_coords(self):
        # 创建对话框
        dialog = tk.Toplevel(self.root)
        dialog.title("偏移坐标")

        # 获取当前屏幕分辨率
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        self.get_screen_scale()

        # 设置对话框尺寸
        if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
            dialog_width = 255 if self.screen_scale == 1.25 else 245
            dialog_height = 180 if self.screen_scale == 1.25 else 185
        elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
            dialog_width = 280
            dialog_height = 195 if self.screen_scale == 1.25 else 185
        else:
            dialog_width = 280
            dialog_height = 200

        # 居中对话框
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")

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

            targets = selected_indices or [self.tree.index(self.tree.selection()[0])] if self.tree.selection() else []
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

            self.update_image_listbox()
            dialog.destroy()

        # 按钮框架
        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=10)

        # 第一行：单独一个“应用于更多步骤”按钮
        apply_btn = ttk.Button(
            btn_frame,
            text="应用于更多步骤",
            command=select_steps,      # 你的处理函数
            bootstyle="primary-outline"
        )
        apply_btn.grid(row=0, column=0, padx=5, pady=5)

        # 第二行：一个子Frame，承载“取消”“保存”两个按钮
        sub_frame = tk.Frame(btn_frame)
        sub_frame.grid(row=1, column=0, pady=5)

        cancel_btn = ttk.Button(
            sub_frame,
            text="取消",
            command=dialog.destroy,
            bootstyle="primary-outline"
        )
        cancel_btn.pack(side=tk.LEFT, padx=5)

        save_btn = ttk.Button(
            sub_frame,
            text="保存",
            command=on_save,
            bootstyle="primary-outline"
        )
        save_btn.pack(side=tk.LEFT, padx=5)
        btn_frame.grid_columnconfigure(0, weight=1)

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
        dialog.title("保存配置")
        
        # 计算居中位置
        main_window_x = self.root.winfo_x()
        main_window_y = self.root.winfo_y()
        main_window_width = self.root.winfo_width()
        main_window_height = self.root.winfo_height()
        
        # 获取屏幕分辨率
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 根据分辨率设置对话框尺寸
        if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
            # 1080p (1920x1080) 到小于 1440p 的情况
            dialog_width = 300
            dialog_height = 120
        elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
            # 1440p (2560x1440) 到小于 2160p (4K) 的情况
            dialog_width = 300
            dialog_height = 130
        else:
            # 其他情况使用默认尺寸
            dialog_width = 300
            dialog_height = 130
        
        x = main_window_x + (main_window_width - dialog_width) // 2
        y = main_window_y + (main_window_height - dialog_height) // 2
        
        dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
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
        dialog.iconbitmap("icon/app.ico")  # 设置窗口图标

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
        dialog.title("选择配置文件")
        
        # 计算居中位置
        main_window_x = self.root.winfo_x()
        main_window_y = self.root.winfo_y()
        main_window_width = self.root.winfo_width()
        main_window_height = self.root.winfo_height()
        
        # 获取屏幕分辨率
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 根据分辨率设置对话框尺寸
        if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
            # 1080p (1920x1080) 到小于 1440p 的情况
            dialog_width = 400
            dialog_height = 300
        elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
            # 1440p (2560x1440) 到小于 2160p (4K) 的情况
            dialog_width = 400
            dialog_height = 310
        else:
            # 其他情况使用默认尺寸
            dialog_width = 400
            dialog_height = 310
        
        x = main_window_x + (main_window_width - dialog_width) // 2
        y = main_window_y + (main_window_height - dialog_height) // 2
        
        dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
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
        dialog.iconbitmap("icon/app.ico")  # 设置窗口图标
        
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

            for img_data in self.image_list:
                # 确保每个项目都有 11 个元素
                while len(img_data) < 11:
                    img_data = img_data + [""]

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
                    ), image=photo)
                    self.tree.image_refs.append(photo)
                except Exception as e:
                    print(f"处理图像时出错 {img_data[0]}: {e}")
                    logging.error(f"处理图像时出错 {img_data[0]}: {e}")
            
            # 更新循环次数输入框
            self.loop_count_entry.delete(0, tk.END)
            self.loop_count_entry.insert(0, str(self.loop_count))
            
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
            config_files = [f for f in os.listdir(working_dir) if f.endswith(".json")]
            if not config_files:
                messagebox.showinfo("提示", "没有找到任何配置文件", parent=self.root)
                return

            # 创建一个 Toplevel 窗口
            export_window = tk.Toplevel(self.root)
            export_window.title("选择导出的配置文件")
            export_window.transient(self.root)
            export_window.grab_set()

            # 计算居中位置
            main_window_x = self.root.winfo_x()
            main_window_y = self.root.winfo_y()
            main_window_width = self.root.winfo_width()
            main_window_height = self.root.winfo_height()
            
            # 获取屏幕分辨率
            screen_width = self.root.winfo_screenwidth()
            screen_height = self.root.winfo_screenheight()
            
            # 根据分辨率设置对话框尺寸
            if screen_width >= 1920 and screen_height >= 1080 and (screen_width < 2560 or screen_height < 1440):
                # 1080p (1920x1080) 到小于 1440p 的情况
                window_width = 400
                window_height = 300
            elif screen_width >= 2560 and screen_height >= 1440 and (screen_width < 3840 or screen_height < 2160):
                # 1440p (2560x1440) 到小于 2160p (4K) 的情况
                window_width = 400
                window_height = 310
            else:
                # 其他情况使用默认尺寸
                window_width = 400
                window_height = 310
            
            x = main_window_x + (main_window_width - window_width) // 2
            y = main_window_y + (main_window_height - window_height) // 2
            
            export_window.geometry(f"{window_width}x{window_height}+{x}+{y}")

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
        messagebox.showinfo("鼠标位置", f"当前鼠标位置: ({x}, {y})")
    
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
                selected_image[6], selected_image[7], selected_image[8], selected_image[9], selected_image[10]
            )
            self.update_image_listbox()
   
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
        self.empty_space_menu.add_command(label="保存配置", command=self.save_config)
        self.empty_space_menu.add_command(label="加载配置", command=self.load_config)
        self.empty_space_menu.add_separator()
        self.empty_space_menu.add_command(label="查看日志", command=self.show_logs)

        # 选中项的菜单
        self.context_menu = tk.Menu(self.root, tearoff=0, postcommand=self.update_context_menu)   
        self.context_menu.add_command(label="重新截图", command=self.retake_screenshot)
        self.context_menu.add_command(label="关闭识图", command=self.Image_recognition_click)  # 默认显示为“关闭识图”，索引1
        self.context_menu.add_command(label="条件跳转", command=self.set_condition_jump)
        self.context_menu.add_separator() #索引3

        self.context_menu.add_command(label="复制", command=self.copy_item)
        self.context_menu.add_command(label="粘贴", command=self.paste_item)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="删除", command=self.delete_selected_image)
        self.context_menu.add_command(label="禁用", command=self.toggle_disable_status)  # 注意保持为“禁用”，索引8
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
            self.context_menu.entryconfig(8, label=new_disable_label, command=self.toggle_disable_status)
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
                selected_image[10] #鼠标动作
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
            ))
            self.update_context_menu()
            self.update_image_listbox()

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
            self.tree.selection_clear()
            self.tree.selection_set(item)
            self.tree.focus(item)
            self.update_context_menu()  # 更新菜单状态
            # 使用after确保菜单在选中后显示
            self.root.after(1, lambda: self.context_menu.post(event.x_root, event.y_root))
        else:  # 点击的是空白处
            self.empty_space_menu.post(event.x_root, event.y_root)
        
        return "break"
   
    def clear_list(self):
        self.reset_to_initial_state()

    def copy_item(self):
        selected_items = self.tree.selection()
        if selected_items:
            index = self.tree.index(selected_items[0])
            original_item = self.image_list[index]
               
            # 创建像文件的副本
            new_image_path = self.create_image_copy(original_item[0])
               
            # 创建新的元组，使用新的图像路径
            self.copied_item = (new_image_path,) + tuple(original_item[1:])
   
    def create_image_copy(self, original_path):
        # 创建图像文件的副本（与原文件同目录）
        dirname = os.path.dirname(original_path)
        base_name = os.path.basename(original_path)
        name, ext = os.path.splitext(base_name)
        new_name = f"{name}_copy{ext}"
        new_path = os.path.join(dirname, new_name)
        shutil.copy2(original_path, new_path)
        return new_path
       
    def paste_item(self):
        if self.copied_item:
            target = self.tree.focus()  # 获取当前选中的项目
            if target:
                target_index = self.tree.index(target)  # 获取当前项目的索引
                new_item = list(self.copied_item)  # 复制项目数据（确保是可变列表）
                self.image_list.insert(target_index + 1, new_item)  # 插入到选中项的下一行
            else:
                new_item = list(self.copied_item)
                self.image_list.append(new_item)  # 如果没有选中项，则添加到末尾
                
            self.update_image_listbox()  # 更新详细信息
     
            # 获取所有项
            all_items = self.tree.get_children()
            if all_items:
                if target:
                    last_item = all_items[target_index + 1]  # 获取新插入的项目
                else:
                    last_item = all_items[-1]  # 如果没有选中项，则聚焦到最后一个项目
                
                self.tree.selection_set(last_item)  # 选择该项目
                self.tree.focus(last_item)  # 聚焦到该项目
                self.tree.see(last_item)  # 滚动到可见区域
                print(f"聚焦到项目: {last_item}")
            else:
                print("没有可用的项目")
            self.update_label() # 更新详细信息

    def edit_similarity_threshold(self):
        selected_items = self.tree.selection()
        if not selected_items:
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = self.image_list[selected_index]

        # 创建对话框（先不显示内容）
        dialog = tk.Toplevel(self.root)
        dialog.title("修改相似度")
        
        # 预设对话框大小
        dialog_width = 300
        dialog_height = 150
        
        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        
        # 设置初始几何位置
        dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
        
        # 设置窗口关系
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.attributes('-topmost', True)

        # 标签和输入框
        label = tk.Label(dialog, text="请输入新的相似度（0 - 1.0）：")
        label.pack(padx=10, pady=10)
        
        entry = tk.Entry(dialog)
        entry.pack(padx=10, pady=10)
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
                selected_image[10]
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
        dialog.iconbitmap("icon/app.ico")  # 设置窗口图标

        # 最终调整窗口大小（如果需要）
        dialog.update_idletasks()
        dialog_width = dialog.winfo_width()
        dialog_height = dialog.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        dialog.geometry(f"+{center_x}+{center_y}")


    def edit_wait_time(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]

            # 创建对话框
            dialog = tk.Toplevel(self.root)
            dialog.title("修改延时ms")
            
            # 先设置窗口大小和位置，再显示内容
            dialog_width = 300  # 根据你的需要调整
            dialog_height = 150  # 根据你的需要调整
            
            # 获取主窗口位置和尺寸
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            main_height = self.root.winfo_height()
            
            # 计算居中位置
            center_x = main_x + (main_width - dialog_width) // 2
            center_y = main_y + (main_height - dialog_height) // 2
            
            # 设置对话框位置和大小
            dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
            
            # 设置窗口关系
            dialog.transient(self.root)
            dialog.grab_set()  # 模态对话框
            dialog.attributes('-topmost', True)  # 让窗口置顶

            # 标签和输入框
            label = tk.Label(dialog, text="请输入新的延时ms（毫秒）：")
            label.pack(padx=10, pady=10)
            entry = tk.Entry(dialog)
            entry.pack(padx=10, pady=10)
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
                    selected_image[10]
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
            dialog.iconbitmap("icon/app.ico")  # 设置窗口图标

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
                selected_image[10]
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
                selected_image[10] #鼠标动作
            )
            
            # 更新界面显示
            self.update_image_listbox()
    
    def edit_image_name(self):
        selected_items = self.tree.selection()
        if selected_items:
            selected_item = selected_items[0]
            selected_index = self.tree.index(selected_item)
            selected_image = self.image_list[selected_index]

            # 创建对话框
            dialog = tk.Toplevel(self.root)
            dialog.title("修改步骤名称")
            
            # 先设置窗口大小和位置，再显示内容
            dialog_width = 300  # 根据你的需要调整
            dialog_height = 150  # 根据你的需要调整
            
            # 获取主窗口位置和尺寸
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            main_height = self.root.winfo_height()
            
            # 计算居中位置
            center_x = main_x + (main_width - dialog_width) // 2
            center_y = main_y + (main_height - dialog_height) // 2
            
            # 设置对话框位置和大小
            dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
            
            # 设置窗口关系
            dialog.transient(self.root)
            dialog.grab_set()  # 模态对话框
            dialog.attributes('-topmost', True)  # 让窗口置顶

            # 标签和输入框
            label = tk.Label(dialog, text="请输入新的步骤名称：")
            label.pack(padx=10, pady=10)
            entry = tk.Entry(dialog)
            entry.pack(padx=10, pady=10)
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
                    selected_image[10]
                )
                self.update_image_listbox()
                dialog.destroy()

            def on_cancel():
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
            dialog.iconbitmap("icon/app.ico")  # 设置窗口图标
   
    def set_condition_jump(self):
        selected_items = self.tree.selection()
        if not selected_items:
            messagebox.showwarning("警告", "请先选择一个项目")
            return

        selected_item = selected_items[0]
        selected_index = self.tree.index(selected_item)
        selected_image = list(self.image_list[selected_index])

        # 创建对话框（先不显示内容）
        dialog = tk.Toplevel(self.root)
        dialog.title("条件跳转")
        
        # 预设对话框大小
        dialog_width = 270
        dialog_height = 190
        
        # 计算居中位置
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        
        # 设置初始几何位置
        dialog.geometry(f"{dialog_width}x{dialog_height}+{center_x}+{center_y}")
        
        # 设置窗口关系
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.attributes('-topmost', True)

        # 条件选择
        condition_frame = tk.Frame(dialog)
        condition_frame.pack(pady=5)
        tk.Label(condition_frame, text="条件为:").pack(side=tk.LEFT)
        
        # 初始化条件值
        current_condition = selected_image[6] if len(selected_image) > 6 else ""
        condition_var = tk.StringVar(value="无" if not current_condition else current_condition)
        condition_combo = ttk.Combobox(
            condition_frame, 
            textvariable=condition_var, 
            values=["识图成功", "识图失败", "无"], 
            width=15
        )
        condition_combo.pack(side=tk.LEFT)

        # 需跳转选择
        jump_frame = tk.Frame(dialog)
        jump_frame.pack(pady=5)
        tk.Label(jump_frame, text="跳转到:").pack(side=tk.LEFT)
        
        # 初始化跳转值
        current_jump = selected_image[7] if len(selected_image) > 7 else ""
        jump_var = tk.StringVar(value="无" if not current_jump else current_jump)
        step_names = ["无"] + [img[1] for img in self.image_list if img[1]]  # 获取所有步骤名称
        jump_combo = ttk.Combobox(
            jump_frame, 
            textvariable=jump_var, 
            values=step_names, 
            width=15
        )
        jump_combo.pack(side=tk.LEFT)

        # 需禁用选择
        disable_frame = tk.Frame(dialog)
        disable_frame.pack(pady=5)
        tk.Label(disable_frame, text="需禁用:").pack(side=tk.LEFT)
        
        # 初始化禁用值
        current_disable = selected_image[9] if len(selected_image) > 9 else ""
        disable_var = tk.StringVar(value="无" if not current_disable else current_disable)
        disable_combo = ttk.Combobox(
            disable_frame, 
            textvariable=disable_var, 
            values=step_names, 
            width=15
        )
        disable_combo.pack(side=tk.LEFT)

        def save_condition():
            condition = condition_var.get()
            jump_to = jump_var.get()
            disable_step = disable_var.get()

            # 映射字符串
            condition = "" if condition == "无" else condition
            jump_to = "" if jump_to == "无" else jump_to
            disable_step = "" if disable_step == "无" else disable_step

            # 验证逻辑
            if (jump_to or disable_step) and not condition:
                messagebox.showwarning("警告", "当设置了跳转或禁用目标时，必须指定条件！", parent=dialog)
                return

            try:
                # 确保列表长度足够
                while len(selected_image) < 10:
                    selected_image.append("")

                selected_image[6] = condition
                selected_image[7] = jump_to
                selected_image[9] = disable_step

                self.image_list[selected_index] = tuple(selected_image)
                self.update_image_listbox()

                # 重新选中项目
                items = self.tree.get_children()
                if selected_index < len(items):
                    self.tree.selection_set(items[selected_index])
                    self.tree.focus(items[selected_index])

                logging.info(f"更新条件跳转设置：条件={condition}, 跳转到={jump_to}, 需禁用={disable_step}")
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
            bootstyle="primary-outline"  # 次要轮廓样式
        )
        cancel_button.pack(side=tk.RIGHT, padx=5)

        # 最终调整窗口大小（如果需要）
        dialog.update_idletasks()
        dialog_width = dialog.winfo_width()
        dialog_height = dialog.winfo_height()
        center_x = main_x + (main_width - dialog_width) // 2
        center_y = main_y + (main_height - dialog_height) // 2
        dialog.geometry(f"+{center_x}+{center_y}")
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
        log_window.title("应用日志")
        
        # 设置窗口大小
        log_width = 700
        log_height = 500
        
        # 获取主窗口位置和尺寸
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        
        # 计算居中位置
        center_x = main_x + (main_width - log_width) // 2
        center_y = main_y + (main_height - log_height) // 2
        
        # 设置日志窗口位置和大小
        log_window.geometry(f"{log_width}x{log_height}+{center_x}+{center_y}")
      
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

        # 确保日志窗口保持在主窗口上方
        log_window.transient(self.root)
        log_window.grab_set()
        log_window.iconbitmap("icon/app.ico")  # 设置窗口图标


if __name__ == "__main__":
    root = tk.Tk()
    app = ImageRecognitionApp(root)
    
    def on_closing():
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