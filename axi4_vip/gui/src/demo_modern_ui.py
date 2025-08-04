#!/usr/bin/env python3
"""
Demo script showing the modern UI enhancements for AMBA Bus Matrix GUI
This demonstrates the ultrathink design aesthetic with animations and modern styling
"""

import tkinter as tk
from tkinter import ttk
import sys
import os

# Add current directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from modern_ui_theme import ModernTheme, apply_modern_theme, ModernButton, ModernCanvas
from bus_matrix_gui_modern import ModernBusMatrixGUI
from vip_gui_integration_modern import ModernVIPControlPanel
from bus_matrix_gui import MasterConfig, SlaveConfig, BusConfig


class ModernUIDemo:
    """Demo application showcasing modern UI features"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("AMBA Modern UI Demo - Ultrathink Design")
        
        # Apply modern theme
        self.theme = apply_modern_theme(root, dark_mode=False)
        
        # Set window size and center
        self.root.geometry("1400x800")
        self.center_window()
        
        # Create UI
        self.setup_ui()
        
        # Load demo configuration
        self.load_demo_config()
        
    def center_window(self):
        """Center window on screen"""
        self.root.update_idletasks()
        width = self.root.winfo_width()
        height = self.root.winfo_height()
        x = (self.root.winfo_screenwidth() // 2) - (width // 2)
        y = (self.root.winfo_screenheight() // 2) - (height // 2)
        self.root.geometry(f'{width}x{height}+{x}+{y}')
        
    def setup_ui(self):
        """Setup demo UI"""
        # Create main container
        main_container = ttk.Frame(self.root, style='Modern.TFrame')
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # Create header
        self.create_header(main_container)
        
        # Create demo selector
        self.create_demo_selector(main_container)
        
        # Create demo area
        self.demo_frame = ttk.Frame(main_container, style='Modern.TFrame')
        self.demo_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Show welcome screen
        self.show_welcome()
        
    def create_header(self, parent):
        """Create modern header"""
        header = tk.Frame(parent, bg=self.theme.get_color('primary'), height=80)
        header.pack(fill=tk.X)
        header.pack_propagate(False)
        
        # Header content
        content = tk.Frame(header, bg=self.theme.get_color('primary'))
        content.place(relx=0.5, rely=0.5, anchor='center')
        
        # Title
        tk.Label(content, text="AMBA Modern UI Demo",
                font=self.theme.FONTS['heading_xl'],
                bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary')).pack()
        
        # Subtitle
        tk.Label(content, text="Experience the ultrathink design aesthetic",
                font=self.theme.FONTS['body'],
                bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary')).pack(pady=(5, 0))
        
        # Theme toggle
        self.theme_btn = tk.Button(header, text="Dark", command=self.toggle_theme,
                                 bg=self.theme.get_color('primary_dark'),
                                 fg=self.theme.get_color('text_on_primary'),
                                 font=('Segoe UI', 20),
                                 bd=0, padx=15, pady=10,
                                 cursor='hand2')
        self.theme_btn.place(relx=0.95, rely=0.5, anchor='center')
        
    def create_demo_selector(self, parent):
        """Create demo selection buttons"""
        selector_frame = tk.Frame(parent, bg=self.theme.get_color('surface_variant'), height=60)
        selector_frame.pack(fill=tk.X, padx=20, pady=(20, 0))
        selector_frame.pack_propagate(False)
        
        # Center buttons
        btn_container = tk.Frame(selector_frame, bg=self.theme.get_color('surface_variant'))
        btn_container.place(relx=0.5, rely=0.5, anchor='center')
        
        # Demo buttons
        demos = [
            ("🏠 Welcome", self.show_welcome),
            ("🔲 Bus Matrix", self.show_bus_matrix),
            ("🧪 VIP Panel", self.show_vip_panel),
            ("🎨 UI Components", self.show_components),
            ("✨ Animations", self.show_animations)
        ]
        
        for text, command in demos:
            ModernButton(btn_container, text=text, command=command,
                       style='secondary', theme=self.theme,
                       width=140, height=40).pack(side=tk.LEFT, padx=5)
            
    def clear_demo_frame(self):
        """Clear current demo content"""
        for widget in self.demo_frame.winfo_children():
            widget.destroy()
            
    def show_welcome(self):
        """Show welcome screen"""
        self.clear_demo_frame()
        
        # Welcome container
        welcome = tk.Frame(self.demo_frame, bg=self.theme.get_color('bg'))
        welcome.pack(fill=tk.BOTH, expand=True)
        
        # Center content
        center = tk.Frame(welcome, bg=self.theme.get_color('bg'))
        center.place(relx=0.5, rely=0.5, anchor='center')
        
        # Welcome icon
        tk.Label(center, text="🎨", font=('Segoe UI', 72),
                bg=self.theme.get_color('bg')).pack(pady=20)
        
        # Welcome text
        tk.Label(center, text="Welcome to AMBA Modern UI",
                font=self.theme.FONTS['heading_large'],
                bg=self.theme.get_color('bg'),
                fg=self.theme.get_color('text_primary')).pack()
        
        tk.Label(center, text="Explore the enhanced user interface with modern design principles",
                font=self.theme.FONTS['body'],
                bg=self.theme.get_color('bg'),
                fg=self.theme.get_color('text_secondary')).pack(pady=(10, 30))
        
        # Feature cards
        features_frame = tk.Frame(center, bg=self.theme.get_color('bg'))
        features_frame.pack()
        
        features = [
            ("🎯", "Clean Design", "Minimalist interface with\nclear visual hierarchy"),
            ("🌈", "Modern Colors", "Carefully selected palettes\nfor light and dark modes"),
            ("✨", "Smooth Animations", "Delightful transitions and\ninteractive feedback"),
            ("📐", "Better Layout", "Improved spacing and\nvisual organization")
        ]
        
        for icon, title, desc in features:
            self.create_feature_card(features_frame, icon, title, desc)
            
    def create_feature_card(self, parent, icon, title, description):
        """Create feature card"""
        card = tk.Frame(parent, bg=self.theme.get_color('surface'),
                       relief=tk.FLAT, bd=0)
        card.pack(side=tk.LEFT, padx=10, pady=10)
        
        # Shadow effect
        shadow = tk.Frame(card, bg=self.theme.get_color('shadow'), height=2)
        shadow.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Card content
        content = tk.Frame(card, bg=self.theme.get_color('surface'),
                         padx=30, pady=25, width=200, height=180)
        content.pack(fill=tk.BOTH, expand=True)
        content.pack_propagate(False)
        
        # Icon
        tk.Label(content, text=icon, font=('Segoe UI', 36),
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('primary')).pack()
        
        # Title
        tk.Label(content, text=title, font=self.theme.FONTS['subheading'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_primary')).pack(pady=(10, 5))
        
        # Description
        tk.Label(content, text=description, font=self.theme.FONTS['caption'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_secondary'),
                justify=tk.CENTER).pack()
        
        # Hover effect
        def on_enter(e):
            content.config(bg=self.theme.get_color('surface_variant'))
            for widget in content.winfo_children():
                widget.config(bg=self.theme.get_color('surface_variant'))
                
        def on_leave(e):
            content.config(bg=self.theme.get_color('surface'))
            for widget in content.winfo_children():
                widget.config(bg=self.theme.get_color('surface'))
                
        card.bind('<Enter>', on_enter)
        card.bind('<Leave>', on_leave)
        
    def show_bus_matrix(self):
        """Show bus matrix demo"""
        self.clear_demo_frame()
        
        # Create embedded bus matrix GUI
        self.bus_gui = EmbeddedBusMatrixDemo(self.demo_frame, self.theme)
        
    def show_vip_panel(self):
        """Show VIP panel demo"""
        self.clear_demo_frame()
        
        # Create mock GUI instance
        class MockGUI:
            def __init__(self, theme):
                self.theme = theme
                self.current_config = BusConfig(
                    bus_type="AXI4",
                    data_width=64,
                    addr_width=32,
                    masters=[],
                    slaves=[],
                    arbitration="QOS"
                )
                
        mock_gui = MockGUI(self.theme)
        
        # Create VIP panel
        vip_panel = ModernVIPControlPanel(self.demo_frame, mock_gui, self.theme)
        
    def show_components(self):
        """Show UI components gallery"""
        self.clear_demo_frame()
        
        # Create scrollable gallery
        canvas = tk.Canvas(self.demo_frame, bg=self.theme.get_color('bg'),
                         highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.demo_frame, orient="vertical",
                                command=canvas.yview,
                                style='Modern.Vertical.TScrollbar')
        gallery_frame = ttk.Frame(canvas, style='Modern.TFrame')
        
        gallery_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=gallery_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Gallery content
        self.create_component_gallery(gallery_frame)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
    def create_component_gallery(self, parent):
        """Create component gallery content"""
        # Title
        tk.Label(parent, text="UI Component Gallery",
                font=self.theme.FONTS['heading_large'],
                bg=self.theme.get_color('bg'),
                fg=self.theme.get_color('text_primary')).pack(pady=20)
        
        # Buttons section
        self.create_gallery_section(parent, "Buttons", self.create_button_examples)
        
        # Input section
        self.create_gallery_section(parent, "Input Fields", self.create_input_examples)
        
        # Progress section
        self.create_gallery_section(parent, "Progress Indicators", self.create_progress_examples)
        
        # Cards section
        self.create_gallery_section(parent, "Cards & Containers", self.create_card_examples)
        
    def create_gallery_section(self, parent, title, content_func):
        """Create gallery section"""
        section = ttk.LabelFrame(parent, text=title, style='Modern.TLabelframe')
        section.pack(fill=tk.X, padx=40, pady=10)
        
        content_frame = tk.Frame(section, bg=self.theme.get_color('surface'), padx=20, pady=20)
        content_frame.pack(fill=tk.X)
        
        content_func(content_frame)
        
    def create_button_examples(self, parent):
        """Create button examples"""
        # Primary button
        ModernButton(parent, text="Primary Button", command=lambda: None,
                   theme=self.theme).pack(side=tk.LEFT, padx=10)
        
        # Secondary button
        ModernButton(parent, text="Secondary Button", command=lambda: None,
                   style='secondary', theme=self.theme).pack(side=tk.LEFT, padx=10)
        
        # Icon button
        ModernButton(parent, text="🚀 With Icon", command=lambda: None,
                   theme=self.theme).pack(side=tk.LEFT, padx=10)
        
        # Small button
        ModernButton(parent, text="Small", command=lambda: None,
                   theme=self.theme, width=80, height=32).pack(side=tk.LEFT, padx=10)
        
        # Large button
        ModernButton(parent, text="Large Button", command=lambda: None,
                   theme=self.theme, width=160, height=50).pack(side=tk.LEFT, padx=10)
        
    def create_input_examples(self, parent):
        """Create input field examples"""
        # Text entry
        ttk.Label(parent, text="Text Input:").grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Entry(parent, style='Modern.TEntry', width=30).grid(row=0, column=1, padx=10, pady=5)
        
        # Combobox
        ttk.Label(parent, text="Dropdown:").grid(row=1, column=0, sticky=tk.W, pady=5)
        combo = ttk.Combobox(parent, values=["Option 1", "Option 2", "Option 3"],
                           style='Modern.TCombobox', width=28)
        combo.grid(row=1, column=1, padx=10, pady=5)
        combo.current(0)
        
        # Spinbox
        ttk.Label(parent, text="Number:").grid(row=2, column=0, sticky=tk.W, pady=5)
        ttk.Spinbox(parent, from_=0, to=100, style='Modern.TEntry', width=30).grid(row=2, column=1, padx=10, pady=5)
        
        # Checkbox
        ttk.Checkbutton(parent, text="Checkbox option", style='Modern.TCheckbutton').grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=5)
        
        # Radio buttons
        radio_var = tk.StringVar(value="option1")
        ttk.Radiobutton(parent, text="Option 1", variable=radio_var, value="option1",
                      style='Modern.TRadiobutton').grid(row=4, column=0, sticky=tk.W, pady=5)
        ttk.Radiobutton(parent, text="Option 2", variable=radio_var, value="option2",
                      style='Modern.TRadiobutton').grid(row=4, column=1, sticky=tk.W, pady=5)
        
    def create_progress_examples(self, parent):
        """Create progress indicator examples"""
        # Progress bar
        tk.Label(parent, text="Progress Bar:", font=self.theme.FONTS['body']).pack(anchor=tk.W)
        
        progress_container = tk.Frame(parent, bg=self.theme.get_color('surface_variant'),
                                    height=8)
        progress_container.pack(fill=tk.X, pady=10)
        
        progress_bar = tk.Frame(progress_container, bg=self.theme.get_color('primary'),
                              height=8, width=200)
        progress_bar.place(x=0, y=0)
        
        # Circular progress (simulated with text)
        circular_frame = tk.Frame(parent, bg=self.theme.get_color('surface'))
        circular_frame.pack(pady=20)
        
        tk.Label(circular_frame, text="75%", font=self.theme.FONTS['heading_large'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('primary')).pack()
        tk.Label(circular_frame, text="Circular Progress", font=self.theme.FONTS['caption'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_secondary')).pack()
        
    def create_card_examples(self, parent):
        """Create card examples"""
        cards_frame = tk.Frame(parent, bg=self.theme.get_color('surface'))
        cards_frame.pack()
        
        # Simple card
        simple_card = tk.Frame(cards_frame, bg=self.theme.get_color('surface_variant'),
                             relief=tk.FLAT, bd=1)
        simple_card.pack(side=tk.LEFT, padx=10, fill=tk.BOTH, expand=True)
        
        tk.Label(simple_card, text="Simple Card", font=self.theme.FONTS['subheading'],
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_primary'),
                padx=20, pady=15).pack()
        
        # Elevated card with shadow
        elevated_frame = tk.Frame(cards_frame, bg=self.theme.get_color('surface'))
        elevated_frame.pack(side=tk.LEFT, padx=10, fill=tk.BOTH, expand=True)
        
        shadow = tk.Frame(elevated_frame, bg=self.theme.get_color('shadow'))
        shadow.place(x=2, y=2, relwidth=1, relheight=1)
        
        elevated_card = tk.Frame(elevated_frame, bg=self.theme.get_color('surface'),
                               relief=tk.FLAT, bd=0)
        elevated_card.place(x=0, y=0, relwidth=1, relheight=1)
        
        tk.Label(elevated_card, text="Elevated Card", font=self.theme.FONTS['subheading'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_primary'),
                padx=20, pady=15).pack()
        
    def show_animations(self):
        """Show animation demos"""
        self.clear_demo_frame()
        
        # Create animation canvas
        canvas = ModernCanvas(self.demo_frame, self.theme, width=800, height=500)
        canvas.pack(pady=20)
        
        # Control panel
        control_frame = tk.Frame(self.demo_frame, bg=self.theme.get_color('bg'))
        control_frame.pack()
        
        # Animation buttons
        animations = [
            ("Slide Animation", lambda: self.demo_slide_animation(canvas)),
            ("Fade Animation", lambda: self.demo_fade_animation(canvas)),
            ("Bounce Animation", lambda: self.demo_bounce_animation(canvas)),
            ("Ripple Effect", lambda: self.demo_ripple_effect(canvas)),
            ("Clear Canvas", lambda: canvas.delete('all'))
        ]
        
        for text, command in animations:
            ModernButton(control_frame, text=text, command=command,
                       theme=self.theme, width=140, height=36).pack(side=tk.LEFT, padx=5)
            
    def demo_slide_animation(self, canvas):
        """Demo slide animation"""
        # Create rectangle
        rect = canvas.create_modern_rect(50, 200, 150, 280, radius=12,
                                       fill=self.theme.get_color('primary'))
        
        # Animate slide
        canvas.animate_item(rect, 'x', 600, duration=500)
        
    def demo_fade_animation(self, canvas):
        """Demo fade animation"""
        # Create circle that fades
        circle = canvas.create_oval(350, 200, 450, 300,
                                  fill=self.theme.get_color('secondary'),
                                  outline='')
        
        # Simulate fade by changing size
        def fade_out(size=50):
            if size > 0:
                cx, cy = 400, 250
                canvas.coords(circle, cx-size, cy-size, cx+size, cy+size)
                canvas.after(20, lambda: fade_out(size-2))
            else:
                canvas.delete(circle)
                
        fade_out()
        
    def demo_bounce_animation(self, canvas):
        """Demo bounce animation"""
        ball = canvas.create_oval(390, 50, 410, 70,
                                fill=self.theme.get_color('accent'),
                                outline='')
        
        def bounce(y=50, velocity=0):
            velocity += 1  # Gravity
            y += velocity
            
            if y > 430:  # Hit bottom
                y = 430
                velocity = -velocity * 0.8  # Bounce with damping
                
            canvas.coords(ball, 390, y, 410, y+20)
            
            if abs(velocity) > 0.5 or y < 430:
                canvas.after(20, lambda: bounce(y, velocity))
                
        bounce()
        
    def demo_ripple_effect(self, canvas):
        """Demo ripple effect"""
        cx, cy = 400, 250
        
        def create_ripple():
            ripple = canvas.create_oval(cx-5, cy-5, cx+5, cy+5,
                                      fill='', outline=self.theme.get_color('primary'),
                                      width=3)
            
            def expand(radius=5):
                if radius < 100:
                    canvas.coords(ripple, cx-radius, cy-radius, cx+radius, cy+radius)
                    opacity = 1 - (radius / 100)
                    width = max(1, int(3 * opacity))
                    canvas.itemconfig(ripple, width=width)
                    canvas.after(20, lambda: expand(radius+3))
                else:
                    canvas.delete(ripple)
                    
            expand()
            
        # Create multiple ripples
        for i in range(3):
            canvas.after(i * 300, create_ripple)
            
    def toggle_theme(self):
        """Toggle between light and dark theme"""
        self.theme.dark_mode = not self.theme.dark_mode
        self.theme.theme = self.theme.DARK_THEME if self.theme.dark_mode else self.theme.LIGHT_THEME
        
        # Update theme
        apply_modern_theme(self.root, self.theme.dark_mode)
        
        # Update theme button
        self.theme_btn.config(
            text="Light" if self.theme.dark_mode else "Dark",
            bg=self.theme.get_color('primary_dark')
        )
        
        # Refresh current demo
        # Note: In production, you'd want to update all widgets with new colors
        
    def load_demo_config(self):
        """Load demo bus configuration"""
        self.demo_config = BusConfig(
            bus_type="AXI4",
            data_width=64,
            addr_width=32,
            masters=[
                MasterConfig(name="CPU", id_width=4, qos_support=True, priority=1),
                MasterConfig(name="DMA", id_width=4, qos_support=True, priority=2),
                MasterConfig(name="GPU", id_width=8, qos_support=True, priority=0)
            ],
            slaves=[
                SlaveConfig(name="DDR4", base_address=0x00000000, size=1024*1024, memory_type="Memory"),
                SlaveConfig(name="SRAM", base_address=0x10000000, size=256, memory_type="Memory", read_latency=0),
                SlaveConfig(name="UART", base_address=0x20000000, size=4, memory_type="Peripheral"),
                SlaveConfig(name="GPIO", base_address=0x20010000, size=4, memory_type="Peripheral")
            ],
            arbitration="QOS"
        )


class EmbeddedBusMatrixDemo(ttk.Frame):
    """Embedded bus matrix demo"""
    
    def __init__(self, parent, theme):
        super().__init__(parent, style='Modern.TFrame')
        self.theme = theme
        self.pack(fill=tk.BOTH, expand=True)
        
        # Create canvas
        self.canvas = ModernCanvas(self, theme, width=800, height=500)
        self.canvas.pack(padx=20, pady=20)
        
        # Add demo components
        self.setup_demo()
        
    def setup_demo(self):
        """Setup demo bus matrix"""
        # Add masters
        masters = [
            ("CPU", 100, 100),
            ("DMA", 100, 220),
            ("GPU", 100, 340)
        ]
        
        for name, x, y in masters:
            self.add_demo_master(name, x, y)
            
        # Add slaves
        slaves = [
            ("DDR4", 600, 100),
            ("SRAM", 600, 220),
            ("UART", 600, 340),
            ("GPIO", 600, 460)
        ]
        
        for name, x, y in slaves:
            self.add_demo_slave(name, x, y)
            
        # Add interconnect
        self.canvas.after(500, self.add_demo_interconnect)
        
    def add_demo_master(self, name, x, y):
        """Add demo master"""
        # Master block
        master = self.canvas.create_modern_rect(x, y, x+140, y+60, radius=10,
                                              fill=self.theme.get_color('primary'),
                                              outline='')
        
        # Icon
        self.canvas.create_text(x+20, y+30, text="M", 
                              font=('Segoe UI', 18, 'bold'),
                              fill=self.theme.get_color('text_on_primary'))
        
        # Name
        self.canvas.create_text(x+70, y+30, text=name,
                              font=self.theme.FONTS['body'],
                              fill=self.theme.get_color('text_on_primary'))
        
        # Animate entrance
        self.canvas.move(master, -200, 0)
        self.canvas.animate_item(master, 'x', x, duration=300)
        
    def add_demo_slave(self, name, x, y):
        """Add demo slave"""
        # Slave block
        slave = self.canvas.create_modern_rect(x, y, x+140, y+60, radius=10,
                                             fill=self.theme.get_color('secondary'),
                                             outline='')
        
        # Icon
        icon = "M" if "RAM" in name or "DDR" in name else "P"
        self.canvas.create_text(x+20, y+30, text=icon,
                              font=('Segoe UI', 18, 'bold'),
                              fill=self.theme.get_color('text_on_primary'))
        
        # Name
        self.canvas.create_text(x+70, y+30, text=name,
                              font=self.theme.FONTS['body'],
                              fill=self.theme.get_color('text_on_primary'))
        
        # Animate entrance
        self.canvas.move(slave, 200, 0)
        self.canvas.animate_item(slave, 'x', x, duration=300)
        
    def add_demo_interconnect(self):
        """Add demo interconnect"""
        # Interconnect
        inter = self.canvas.create_modern_rect(350, 250, 450, 310, radius=15,
                                             fill=self.theme.get_color('accent'),
                                             outline='')
        
        # Icon
        self.canvas.create_text(400, 280, text="⚡",
                              font=('Segoe UI', 24),
                              fill=self.theme.get_color('text_on_primary'))
        
        # Draw connections
        self.canvas.after(300, self.draw_demo_connections)
        
    def draw_demo_connections(self):
        """Draw demo connections"""
        # Master connections
        for y in [130, 250, 370]:
            self.canvas.create_line(240, y, 350, 280,
                                  fill=self.theme.get_color('primary'),
                                  width=2, smooth=True)
            
        # Slave connections
        for y in [130, 250, 370, 490]:
            self.canvas.create_line(450, 280, 600, y,
                                  fill=self.theme.get_color('secondary'),
                                  width=2, smooth=True)


def main():
    """Main entry point"""
    root = tk.Tk()
    app = ModernUIDemo(root)
    root.mainloop()


if __name__ == "__main__":
    main()