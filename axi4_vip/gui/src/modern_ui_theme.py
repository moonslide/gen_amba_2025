#!/usr/bin/env python3
"""
Modern UI Theme for AMBA Bus Matrix GUI
Implements a modern design aesthetic with smooth animations and styling
"""

import tkinter as tk
from tkinter import ttk, font
import math
from typing import Dict, Tuple, Optional, Callable
import time

class ModernTheme:
    """Modern design theme"""
    
    # Color Schemes
    LIGHT_THEME = {
        # Primary colors
        'bg': '#FAFAFA',
        'surface': '#FFFFFF',
        'surface_variant': '#F5F5F5',
        'primary': '#1976D2',
        'primary_light': '#42A5F5',
        'primary_dark': '#0D47A1',
        'secondary': '#00ACC1',
        'accent': '#FF5252',
        
        # Text colors
        'text_primary': '#212121',
        'text_secondary': '#757575',
        'text_disabled': '#BDBDBD',
        'text_on_primary': '#FFFFFF',
        
        # Status colors
        'success': '#4CAF50',
        'warning': '#FFC107',
        'error': '#F44336',
        'info': '#2196F3',
        
        # Border and shadow
        'border': '#E0E0E0',
        'shadow': 'rgba(0, 0, 0, 0.1)',
        'hover_overlay': 'rgba(0, 0, 0, 0.04)',
        
        # Canvas colors
        'canvas_bg': '#FAFAFA',
        'grid_line': '#EEEEEE',
        'selection': 'rgba(25, 118, 210, 0.12)',
    }
    
    DARK_THEME = {
        # Primary colors
        'bg': '#121212',
        'surface': '#1E1E1E',
        'surface_variant': '#2C2C2C',
        'primary': '#90CAF9',
        'primary_light': '#BBDEFB',
        'primary_dark': '#42A5F5',
        'secondary': '#80DEEA',
        'accent': '#FF8A80',
        
        # Text colors
        'text_primary': '#FFFFFF',
        'text_secondary': '#B3B3B3',
        'text_disabled': '#666666',
        'text_on_primary': '#000000',
        
        # Status colors
        'success': '#81C784',
        'warning': '#FFD54F',
        'error': '#EF5350',
        'info': '#64B5F6',
        
        # Border and shadow
        'border': '#404040',
        'shadow': 'rgba(0, 0, 0, 0.3)',
        'hover_overlay': 'rgba(255, 255, 255, 0.08)',
        
        # Canvas colors
        'canvas_bg': '#1A1A1A',
        'grid_line': '#2A2A2A',
        'selection': 'rgba(144, 202, 249, 0.16)',
    }
    
    # Typography
    FONTS = {
        'heading_xl': ('Segoe UI', 24, 'normal'),
        'heading_large': ('Segoe UI', 20, 'normal'),
        'heading': ('Segoe UI', 16, 'normal'),
        'subheading': ('Segoe UI', 14, 'normal'),
        'body': ('Segoe UI', 12, 'normal'),
        'body_small': ('Segoe UI', 11, 'normal'),
        'caption': ('Segoe UI', 10, 'normal'),
        'button': ('Segoe UI', 12, 'normal'),
        'mono': ('Consolas', 11, 'normal'),
    }
    
    # Spacing and dimensions
    SPACING = {
        'tiny': 4,
        'small': 8,
        'medium': 16,
        'large': 24,
        'xl': 32,
    }
    
    # Animation parameters
    ANIMATION = {
        'duration_fast': 150,  # ms
        'duration_normal': 250,  # ms
        'duration_slow': 350,  # ms
        'easing': 'ease-in-out',
    }
    
    # Border radius
    RADIUS = {
        'small': 4,
        'medium': 8,
        'large': 12,
        'xl': 16,
        'round': 999,
    }
    
    # Shadow definitions
    SHADOWS = {
        'small': '0 1px 3px rgba(0,0,0,0.12), 0 1px 2px rgba(0,0,0,0.24)',
        'medium': '0 3px 6px rgba(0,0,0,0.15), 0 2px 4px rgba(0,0,0,0.12)',
        'large': '0 10px 20px rgba(0,0,0,0.15), 0 3px 6px rgba(0,0,0,0.10)',
        'xl': '0 15px 25px rgba(0,0,0,0.15), 0 5px 10px rgba(0,0,0,0.05)',
    }
    
    def __init__(self, dark_mode: bool = False):
        self.dark_mode = dark_mode
        self.theme = self.DARK_THEME if dark_mode else self.LIGHT_THEME
        self._style = None
        
    def get_color(self, color_name: str) -> str:
        """Get color from current theme"""
        return self.theme.get(color_name, '#000000')
    
    def apply_to_ttk(self, root: tk.Tk):
        """Apply theme to ttk widgets"""
        self._style = ttk.Style(root)
        
        # Configure notebook style
        self._style.configure('Modern.TNotebook', 
                            background=self.get_color('bg'),
                            borderwidth=0)
        self._style.configure('Modern.TNotebook.Tab',
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_secondary'),
                            padding=[20, 12],
                            borderwidth=0,
                            focuscolor='none')
        self._style.map('Modern.TNotebook.Tab',
                       background=[('selected', self.get_color('surface')),
                                 ('active', self.get_color('surface_variant'))],
                       foreground=[('selected', self.get_color('primary')),
                                 ('active', self.get_color('text_primary'))])
        
        # Configure frame style
        self._style.configure('Modern.TFrame',
                            background=self.get_color('bg'),
                            borderwidth=0)
        
        # Configure label frame
        self._style.configure('Modern.TLabelframe',
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_primary'),
                            borderwidth=1,
                            relief='flat',
                            bordercolor=self.get_color('border'))
        self._style.configure('Modern.TLabelframe.Label',
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_secondary'))
        
        # Configure button style
        self._style.configure('Modern.TButton',
                            background=self.get_color('primary'),
                            foreground=self.get_color('text_on_primary'),
                            borderwidth=0,
                            focuscolor='none',
                            padding=[16, 8])
        self._style.map('Modern.TButton',
                       background=[('active', self.get_color('primary_dark')),
                                 ('pressed', self.get_color('primary_dark'))])
        
        # Configure secondary button
        self._style.configure('Secondary.TButton',
                            background=self.get_color('surface_variant'),
                            foreground=self.get_color('text_primary'),
                            borderwidth=1,
                            relief='flat',
                            bordercolor=self.get_color('border'),
                            focuscolor='none',
                            padding=[16, 8])
        self._style.map('Secondary.TButton',
                       background=[('active', self.get_color('surface'))],
                       bordercolor=[('active', self.get_color('primary'))])
        
        # Configure entry style
        self._style.configure('Modern.TEntry',
                            fieldbackground=self.get_color('surface'),
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_primary'),
                            borderwidth=1,
                            relief='flat',
                            bordercolor=self.get_color('border'),
                            insertcolor=self.get_color('primary'))
        self._style.map('Modern.TEntry',
                       bordercolor=[('focus', self.get_color('primary'))])
        
        # Configure combobox style
        self._style.configure('Modern.TCombobox',
                            fieldbackground=self.get_color('surface'),
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_primary'),
                            borderwidth=1,
                            relief='flat',
                            bordercolor=self.get_color('border'),
                            arrowcolor=self.get_color('text_secondary'))
        self._style.map('Modern.TCombobox',
                       bordercolor=[('focus', self.get_color('primary'))],
                       arrowcolor=[('focus', self.get_color('primary'))])
        
        # Configure treeview style
        self._style.configure('Modern.Treeview',
                            background=self.get_color('surface'),
                            foreground=self.get_color('text_primary'),
                            fieldbackground=self.get_color('surface'),
                            borderwidth=0,
                            rowheight=32)
        self._style.configure('Modern.Treeview.Heading',
                            background=self.get_color('surface_variant'),
                            foreground=self.get_color('text_secondary'),
                            borderwidth=0,
                            relief='flat')
        self._style.map('Modern.Treeview',
                       background=[('selected', self.get_color('selection'))],
                       foreground=[('selected', self.get_color('primary'))])
        
        # Configure scrollbar
        self._style.configure('Modern.Vertical.TScrollbar',
                            background=self.get_color('surface_variant'),
                            troughcolor=self.get_color('surface_variant'),
                            borderwidth=0,
                            arrowcolor=self.get_color('text_secondary'),
                            width=12)
        self._style.map('Modern.Vertical.TScrollbar',
                       background=[('active', self.get_color('border'))])
        
        # Configure radiobutton
        self._style.configure('Modern.TRadiobutton',
                            background=self.get_color('bg'),
                            foreground=self.get_color('text_primary'),
                            focuscolor='none')
        
        # Configure checkbutton
        self._style.configure('Modern.TCheckbutton',
                            background=self.get_color('bg'),
                            foreground=self.get_color('text_primary'),
                            focuscolor='none')
        
        # Configure progressbar
        self._style.configure('Modern.Horizontal.TProgressbar',
                            background=self.get_color('primary'),
                            troughcolor=self.get_color('surface_variant'),
                            borderwidth=0,
                            lightcolor=self.get_color('primary_light'),
                            darkcolor=self.get_color('primary'))


class AnimatedWidget:
    """Base class for animated widgets"""
    
    def __init__(self, widget: tk.Widget):
        self.widget = widget
        self._animations = {}
        
    def animate_property(self, property_name: str, start_value: float, end_value: float, 
                        duration: int = 250, easing: str = 'ease-in-out', 
                        callback: Optional[Callable] = None):
        """Animate a numeric property"""
        # Cancel existing animation for this property
        if property_name in self._animations:
            self.widget.after_cancel(self._animations[property_name])
            
        start_time = time.time()
        
        def update_animation():
            current_time = time.time()
            elapsed = (current_time - start_time) * 1000  # Convert to ms
            
            if elapsed >= duration:
                # Animation complete
                setattr(self.widget, property_name, end_value)
                if property_name in self._animations:
                    del self._animations[property_name]
                if callback:
                    callback()
            else:
                # Calculate progress with easing
                progress = elapsed / duration
                eased_progress = self._apply_easing(progress, easing)
                
                # Calculate current value
                current_value = start_value + (end_value - start_value) * eased_progress
                setattr(self.widget, property_name, current_value)
                
                # Schedule next update
                self._animations[property_name] = self.widget.after(16, update_animation)  # ~60 FPS
                
        update_animation()
        
    def _apply_easing(self, t: float, easing: str) -> float:
        """Apply easing function to animation progress"""
        if easing == 'linear':
            return t
        elif easing == 'ease-in':
            return t * t
        elif easing == 'ease-out':
            return 1 - (1 - t) * (1 - t)
        elif easing == 'ease-in-out':
            if t < 0.5:
                return 2 * t * t
            else:
                return 1 - pow(-2 * t + 2, 2) / 2
        elif easing == 'bounce':
            if t < 0.5:
                return (1 - self._bounce_out(1 - 2 * t)) / 2
            else:
                return (1 + self._bounce_out(2 * t - 1)) / 2
        return t
        
    def _bounce_out(self, t: float) -> float:
        """Bounce easing function"""
        if t < 1 / 2.75:
            return 7.5625 * t * t
        elif t < 2 / 2.75:
            t -= 1.5 / 2.75
            return 7.5625 * t * t + 0.75
        elif t < 2.5 / 2.75:
            t -= 2.25 / 2.75
            return 7.5625 * t * t + 0.9375
        else:
            t -= 2.625 / 2.75
            return 7.5625 * t * t + 0.984375


class ModernButton(tk.Canvas):
    """Modern animated button with ripple effect"""
    
    def __init__(self, parent, text: str, command: Optional[Callable] = None,
                 style: str = 'primary', theme: ModernTheme = None, **kwargs):
        self.theme = theme or ModernTheme()
        self.text = text
        self.command = command
        self.style = style
        
        # Set default dimensions
        width = kwargs.pop('width', 120)
        height = kwargs.pop('height', 40)
        
        super().__init__(parent, width=width, height=height, 
                        bg=self.theme.get_color('bg'), 
                        highlightthickness=0, **kwargs)
        
        self._setup_button()
        self._bind_events()
        
    def _setup_button(self):
        """Setup button appearance"""
        # Get colors based on style
        if self.style == 'primary':
            self.bg_color = self.theme.get_color('primary')
            self.text_color = self.theme.get_color('text_on_primary')
            self.hover_color = self.theme.get_color('primary_dark')
        else:
            self.bg_color = self.theme.get_color('surface_variant')
            self.text_color = self.theme.get_color('text_primary')
            self.hover_color = self.theme.get_color('surface')
            
        # Draw button background
        self.bg_rect = self.create_rectangle(0, 0, self.winfo_reqwidth(), self.winfo_reqheight(),
                                           fill=self.bg_color, outline='', tags='bg')
        
        # Draw button text
        self.text_item = self.create_text(self.winfo_reqwidth() // 2, self.winfo_reqheight() // 2,
                                        text=self.text, fill=self.text_color,
                                        font=self.theme.FONTS['button'], tags='text')
        
    def _bind_events(self):
        """Bind mouse events"""
        self.bind('<Enter>', self._on_enter)
        self.bind('<Leave>', self._on_leave)
        self.bind('<Button-1>', self._on_click)
        self.bind('<ButtonRelease-1>', self._on_release)
        
    def _on_enter(self, event):
        """Mouse enter effect"""
        self.itemconfig(self.bg_rect, fill=self.hover_color)
        self.config(cursor='hand2')
        
    def _on_leave(self, event):
        """Mouse leave effect"""
        self.itemconfig(self.bg_rect, fill=self.bg_color)
        self.config(cursor='')
        
    def _on_click(self, event):
        """Click effect with ripple"""
        # Create ripple effect
        x, y = event.x, event.y
        ripple = self.create_oval(x-2, y-2, x+2, y+2, 
                                fill='', outline=self.text_color, width=2)
        
        # Animate ripple
        self._animate_ripple(ripple, x, y)
        
    def _on_release(self, event):
        """Execute command on release"""
        if self.command:
            self.command()
            
    def _animate_ripple(self, ripple, x, y, radius=2, max_radius=50):
        """Animate ripple effect"""
        if radius < max_radius:
            self.coords(ripple, x-radius, y-radius, x+radius, y+radius)
            opacity = 1 - (radius / max_radius)
            # Simulate opacity with stipple (tkinter limitation)
            if opacity < 0.3:
                self.delete(ripple)
            else:
                self.after(10, lambda: self._animate_ripple(ripple, x, y, radius+3, max_radius))
        else:
            self.delete(ripple)


class ModernCanvas(tk.Canvas):
    """Enhanced canvas with modern styling and smooth animations"""
    
    def __init__(self, parent, theme: ModernTheme = None, **kwargs):
        self.theme = theme or ModernTheme()
        
        # Apply theme colors
        kwargs['bg'] = self.theme.get_color('canvas_bg')
        kwargs['highlightthickness'] = 0
        
        super().__init__(parent, **kwargs)
        
        # Animation tracking
        self._animations = {}
        self._hover_items = {}
        
        # Grid settings
        self.grid_visible = True
        self.grid_size = 20
        self.grid_items = []
        
        # Setup grid
        self._draw_grid()
        
    def _draw_grid(self):
        """Draw background grid"""
        if not self.grid_visible:
            return
            
        # Clear existing grid
        for item in self.grid_items:
            self.delete(item)
        self.grid_items.clear()
        
        # Get canvas dimensions
        width = self.winfo_reqwidth() or 800
        height = self.winfo_reqheight() or 600
        
        # Draw vertical lines
        for x in range(0, width, self.grid_size):
            line = self.create_line(x, 0, x, height,
                                  fill=self.theme.get_color('grid_line'),
                                  tags='grid')
            self.grid_items.append(line)
            
        # Draw horizontal lines
        for y in range(0, height, self.grid_size):
            line = self.create_line(0, y, width, y,
                                  fill=self.theme.get_color('grid_line'),
                                  tags='grid')
            self.grid_items.append(line)
            
        # Move grid to back
        self.tag_lower('grid')
        
    def animate_item(self, item, property_name: str, end_value, duration: int = 250):
        """Animate canvas item property"""
        # Get current value
        if property_name in ['x', 'y']:
            coords = self.coords(item)
            current_value = coords[0] if property_name == 'x' else coords[1]
        else:
            current_value = 0  # Default
            
        # Cancel existing animation
        if (item, property_name) in self._animations:
            self.after_cancel(self._animations[(item, property_name)])
            
        start_time = time.time()
        start_value = current_value
        
        def update():
            elapsed = (time.time() - start_time) * 1000
            if elapsed >= duration:
                # Animation complete
                if property_name in ['x', 'y']:
                    coords = list(self.coords(item))
                    if property_name == 'x':
                        dx = end_value - coords[0]
                        self.move(item, dx, 0)
                    else:
                        dy = end_value - coords[1]
                        self.move(item, 0, dy)
                del self._animations[(item, property_name)]
            else:
                # Calculate progress
                progress = elapsed / duration
                # Ease in-out
                if progress < 0.5:
                    eased = 2 * progress * progress
                else:
                    eased = 1 - pow(-2 * progress + 2, 2) / 2
                    
                current = start_value + (end_value - start_value) * eased
                
                if property_name in ['x', 'y']:
                    coords = list(self.coords(item))
                    if property_name == 'x':
                        dx = current - coords[0]
                        self.move(item, dx, 0)
                    else:
                        dy = current - coords[1]
                        self.move(item, 0, dy)
                        
                # Schedule next update
                self._animations[(item, property_name)] = self.after(16, update)
                
        update()
        
    def create_modern_rect(self, x1, y1, x2, y2, radius=8, **kwargs):
        """Create rounded rectangle"""
        points = []
        
        # Top left
        points.extend([x1, y1 + radius])
        points.extend([x1, y1 + radius, x1, y1 + radius, x1 + radius, y1])
        
        # Top right
        points.extend([x2 - radius, y1])
        points.extend([x2 - radius, y1, x2 - radius, y1, x2, y1 + radius])
        
        # Bottom right
        points.extend([x2, y2 - radius])
        points.extend([x2, y2 - radius, x2, y2 - radius, x2 - radius, y2])
        
        # Bottom left
        points.extend([x1 + radius, y2])
        points.extend([x1 + radius, y2, x1 + radius, y2, x1, y2 - radius])
        
        return self.create_polygon(points, smooth=True, **kwargs)


def apply_modern_theme(root: tk.Tk, dark_mode: bool = False):
    """Apply modern theme to entire application"""
    theme = ModernTheme(dark_mode)
    
    # Configure root window
    root.configure(bg=theme.get_color('bg'))
    
    # Apply ttk styles
    theme.apply_to_ttk(root)
    
    return theme