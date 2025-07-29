# AMBA Bus Matrix Configuration Tool

一個全功能的AMBA匯流排矩陣配置工具，支援AXI4、AXI3、AHB和APB協議的RTL生成和驗證環境創建。

## 📂 專案結構 (已重新整理)

```
axi4_vip/gui/
├── README.md                          # 此說明文檔  
├── requirements.txt                   # Python依賴清單
├── 
├── src/                              # 核心程式碼
│   ├── bus_matrix_gui.py            # 主GUI應用程式
│   ├── axi_verilog_generator.py     # RTL生成器
│   ├── vip_environment_generator.py # VIP生成器  
│   └── ...                          # 其他核心模組 (60+ 檔案)
│
├── docs/                            # 📖 文檔目錄 (已整理)
│   ├── AMBA_Bus_Matrix_Complete_User_Guide.pdf    # 🎯 完整用戶指南 (92頁)
│   ├── user_guide_generator/        # PDF生成系統
│   │   ├── create_complete_guide.py # 主要PDF生成器
│   │   ├── sections/               # 各章節實作 (7個模組)
│   │   └── assets/                 # 圖片和資源
│   │       ├── screenshots/        # 真實GUI截圖 (15張)
│   │       └── backup_mockups/     # 備份mockup圖片
│   └── reports/                    # 開發報告 (歸檔，25+ 文檔)
│
├── examples/                       # 🎯 使用範例
│   ├── simple_system/             # 簡單系統範例
│   ├── batch_generation.py        # 批次生成範例
│   └── performance_analysis.py    # 性能分析範例
│
├── templates/                      # 📋 配置模板
│   ├── simple_axi4_2m3s.json     # 簡單AXI4模板
│   ├── complex_axi4_system.json  # 複雜AXI4系統
│   └── ahb_system.json           # AHB系統模板
│
├── tests/                         # 🧪 測試檔案 (已整理)
│   ├── unit_tests/               # 單元測試 (6個測試)
│   ├── integration_tests/        # 整合測試
│   └── test_data/               # 測試數據和輸出
│
├── output/                       # 📦 生成的檔案
│   ├── rtl/                     # RTL輸出
│   └── vip/                     # VIP輸出
│
└── scripts/                     # 🔧 工具腳本 (已整理)
    ├── launch_gui.sh            # GUI啟動腳本
    ├── generate_user_guide.sh   # 用戶指南生成腳本
    └── ...                      # 其他工具腳本 (8個腳本)
```

## 🚀 快速開始

### 1. 環境要求

- Python 3.6+
- tkinter (GUI界面)
- matplotlib >= 3.0 (圖表生成)
- numpy >= 1.15 (數值計算)

### 2. 安裝依賴

```bash
pip3 install -r requirements.txt
```

### 3. 啟動GUI

```bash
# 方法1: 使用啟動腳本 (推薦)
./scripts/launch_gui.sh

# 方法2: 直接執行
python3 src/bus_matrix_gui.py
```

### 4. 生成完整用戶指南

```bash
# 生成92頁完整PDF用戶指南
./scripts/generate_user_guide.sh

# 或手動執行
cd docs/user_guide_generator
python3 create_complete_guide.py
```

## 🎯 主要功能

### 🔧 RTL生成
- ✅ 支援AXI4/AXI3/AHB/APB協議
- ✅ 2-32個主設備，2-64個從設備
- ✅ 自動地址解碼和仲裁器生成
- ✅ SystemVerilog/Verilog輸出
- ✅ 綜合友好的RTL代碼
- ✅ TrustZone安全支援

### 🧪 VIP生成 
- ✅ 完整的UVM驗證環境
- ✅ 協議合規性檢查
- ✅ 覆蓋率模型和斷言
- ✅ 性能分析工具
- ✅ 回歸測試框架
- ✅ 支援VCS/Questa/Xcelium

### 🖥️ GUI工具
- ✅ 視覺化匯流排矩陣設計
- ✅ 拖放式組件配置
- ✅ 即時設計驗證
- ✅ 專案管理功能
- ✅ JSON配置檔案支援

## 📖 快速使用範例

### 範例1: 創建簡單的AXI4系統

```python
from src.bus_config import BusConfiguration

# 創建配置
config = BusConfiguration()
config.set_protocol("AXI4")
config.add_master("cpu", master_type="cpu")
config.add_master("dma", master_type="dma") 
config.add_slave("memory", base_addr="0x00000000", size="1GB")
config.add_slave("peripheral", base_addr="0x40000000", size="256MB")

# 生成RTL
from src.axi_verilog_generator import AXIVerilogGenerator
generator = AXIVerilogGenerator(config)
generator.generate_rtl("output/rtl/")
```

### 範例2: 使用JSON配置文件

```bash
python3 src/bus_matrix_gui.py --config templates/simple_axi4_2m3s.json
```

### 範例3: 批次生成多個配置

```python
# 使用examples中的批次生成腳本
python3 examples/batch_generation.py
```

## 📚 完整文檔

### 📄 用戶指南 (92頁完整版)
**位置**: `docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf`

**內容包括**:
- 📖 第1章: 入門指南 (10頁)
- 🔄 第2章: 完整工作流程 (11頁) 
- ⚡ 第3章: RTL生成 (13頁)
- 🧪 第4章: VIP生成 (18頁)
- 🚀 第5章: 高級功能 (10頁)
- ⚙️ 第6章: 配置參考 (4頁)
- 🛠️ 第7章: 故障排除 (7頁)
- 📡 第8章: API參考 (5頁)
- 📋 附錄: 協議規範與模板 (11頁)

### 🎯 重點章節快速導航
- **新手入門**: 第1章 + 第2章 (21頁)
- **RTL開發**: 第3章 + 第6章 (17頁)
- **驗證環境**: 第4章 + 第7章 (25頁)
- **高級配置**: 第5章 + 第8章 + 附錄 (26頁)

## 🔧 高級功能

### 🔒 TrustZone安全支援
- 安全/非安全域分離
- 安全存取控制
- 地址範圍保護
- ASIL-D汽車安全等級支援

### ⚡ QoS管理
- 16級優先等級 (0-15)
- 頻寬分配和調節
- 飢餓預防機制
- 即時系統支援

### 🕰️ 多時鐘域支援
- 異步時鐘域跨越
- CDC(Clock Domain Crossing)處理
- 時序優化和流水線配置
- DVFS(動態電壓頻率縮放)支援

### 📊 性能優化
- 流水線深度可配置 (0-8級)
- 延遲最小化模式
- 吞吐量分析工具
- 資源使用優化

## 🧪 測試與驗證

### 運行測試套件

```bash
# 運行所有單元測試
python3 -m pytest tests/unit_tests/ -v

# 測試RTL生成
python3 tests/unit_tests/test_verilog_syntax_fix.py

# 測試VIP生成
python3 tests/unit_tests/test_vip_generation_fixes.py

# 驗證配置解析
python3 tests/unit_tests/test_pcwm_fix.py
```

### RTL綜合驗證

```bash
# 檢查生成的RTL語法
python3 tests/unit_tests/test_syntax_fix_simple.py

# 運行簡單的RTL生成測試
python3 examples/create_simple_system.py
```

## 🛠️ 專案維護與整理

### ✅ 最新整理成果 (v2.0.0)

本專案剛完成大規模重新整理：

1. **檔案結構優化** ✅
   - 移除了20+ 重複的PDF生成器檔案
   - 整理了25+ 散亂的文檔報告
   - 重新組織了測試檔案結構
   - 清理了備份和臨時檔案

2. **文檔系統完善** ✅
   - 完成92頁完整用戶指南
   - 整合所有技術文檔
   - 添加真實GUI截圖
   - 建立完整的參考資料

3. **功能驗證** ✅
   - PDF生成器測試通過
   - 所有import路徑已修正
   - 腳本執行權限已設置
   - 核心功能保持完整

## 📝 版本歷史

### v2.0.0 (當前版本) - 完整重構
- ✅ 92頁完整用戶指南生成系統
- ✅ 重新整理的專案結構
- ✅ 改進的檔案組織和路徑管理
- ✅ 增強的測試覆蓋率
- ✅ 完整的文檔體系

### v1.5.0 - 功能擴展
- TrustZone安全支援
- QoS管理功能  
- 多協議支援
- VIP增強功能

## 🆘 支援與聯繫

- **主要文檔**: `docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf` (92頁)
- **快速範例**: `examples/` 目錄
- **API參考**: 用戶指南第8章
- **故障排除**: 用戶指南第7章
- **配置模板**: `templates/` 目錄

## 📄 許可證

BSD-2-Clause許可證 - 可用於商業和開源專案。

---

## 🎯 重要提示

- **RTL代碼**: 已通過綜合驗證，可用於FPGA和ASIC實現
- **VIP環境**: 支援主流模擬器 (VCS、Questa、Xcelium)  
- **協議合規**: 符合AMBA AXI4/AXI3/AHB/APB規範
- **文檔完整**: 92頁技術文檔涵蓋所有功能細節

**開始使用**: 直接執行 `./scripts/launch_gui.sh` 啟動圖形界面！