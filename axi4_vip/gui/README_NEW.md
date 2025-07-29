# AMBA Bus Matrix Configuration Tool

一個全功能的AMBA匯流排矩陣配置工具，支援AXI4、AXI3、AHB和APB協議的RTL生成和驗證環境創建。

## 📂 專案結構

```
axi4_vip/gui/
├── README.md                          # 此說明文檔
├── requirements.txt                   # Python依賴清單
├── 
├── src/                              # 核心程式碼
│   ├── bus_matrix_gui.py            # 主GUI應用程式
│   ├── axi_verilog_generator.py     # RTL生成器
│   ├── vip_environment_generator.py # VIP生成器  
│   └── ...                          # 其他核心模組
│
├── docs/                            # 文檔目錄
│   ├── AMBA_Bus_Matrix_Complete_User_Guide.pdf    # 完整用戶指南(92頁)
│   ├── user_guide_generator/        # PDF生成器
│   │   ├── create_complete_guide.py # 主要生成器
│   │   ├── sections/               # 各章節實作
│   │   └── assets/                 # 圖片和資源
│   └── reports/                    # 開發報告(歸檔)
│
├── examples/                       # 使用範例
│   ├── simple_system/             # 簡單系統範例
│   ├── automotive_soc/            # 汽車SoC範例
│   └── datacenter_config/         # 數據中心配置
│
├── templates/                      # 配置模板
│   ├── simple_axi4_2m3s.json     # 簡單AXI4模板
│   ├── complex_axi4_system.json  # 複雜AXI4系統
│   └── ahb_system.json           # AHB系統模板
│
├── tests/                         # 測試文件
│   ├── unit_tests/               # 單元測試
│   ├── integration_tests/        # 整合測試
│   └── test_data/               # 測試數據
│
├── output/                       # 生成的文件
│   ├── rtl/                     # RTL輸出
│   └── vip/                     # VIP輸出
│
└── scripts/                     # 工具腳本
    ├── launch_gui.sh            # GUI啟動腳本
    ├── generate_user_guide.sh   # 用戶指南生成
    └── ...                      # 其他工具腳本
```

## 🚀 快速開始

### 1. 環境要求

- Python 3.6+
- tkinter (通常隨Python安裝)
- matplotlib >= 3.0
- numpy >= 1.15

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

### 4. 生成用戶指南

```bash
./scripts/generate_user_guide.sh
```

## 🎯 主要功能

### RTL生成
- 支援AXI4/AXI3/AHB/APB協議
- 可配置的主設備和從設備數量
- 自動地址映射和仲裁器生成
- SystemVerilog/Verilog輸出
- 綜合友好的RTL代碼

### VIP生成
- 完整的UVM驗證環境
- 協議合規性檢查
- 覆蓋率模型
- 性能分析工具
- 回歸測試框架

### GUI工具
- 視覺化匯流排矩陣設計
- 拖放式組件配置
- 即時設計驗證
- 專案管理功能
- 配置文件導入/導出

## 📖 使用範例

### 創建簡單的AXI4系統

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

### 使用JSON配置文件

```bash
python3 src/bus_matrix_gui.py --config templates/simple_axi4_2m3s.json
```

## 🔧 高級功能

### TrustZone安全支援
- 安全/非安全域分離
- 安全存取控制
- 地址範圍保護

### QoS管理
- 可配置的優先級
- 頻寬分配
- 飢餓預防機制

### 多時鐘域支援
- 異步時鐘域跨越
- CDC(Clock Domain Crossing)處理
- 時序優化

### 性能優化
- 流水線深度配置
- 延遲優化
- 吞吐量分析

## 📚 文檔

- **完整用戶指南**: `docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf` (92頁)
- **API參考**: 用戶指南第8章
- **配置參考**: 用戶指南第6章
- **故障排除**: 用戶指南第7章

## 🧪 測試

### 運行單元測試
```bash
python3 -m pytest tests/unit_tests/
```

### 運行整合測試
```bash
python3 -m pytest tests/integration_tests/
```

### 驗證RTL生成
```bash
python3 tests/unit_tests/test_verilog_syntax_fix.py
```

## 🛠️ 開發

### 貢獻指南
1. Fork專案
2. 創建功能分支 (`git checkout -b feature/new-feature`)
3. 提交更改 (`git commit -am 'Add new feature'`)
4. 推送到分支 (`git push origin feature/new-feature`)
5. 創建Pull Request

### 代碼結構
- `src/`: 核心應用程式邏輯
- `docs/user_guide_generator/`: PDF文檔生成系統
- `examples/`: 使用範例和模板
- `tests/`: 測試套件
- `scripts/`: 工具和自動化腳本

## 📝 更新日誌

### v2.0.0 (最新)
- ✅ 完整92頁用戶指南
- ✅ 重新整理的專案結構
- ✅ 改進的GUI界面
- ✅ 增強的VIP生成
- ✅ 全面的測試覆蓋

### v1.5.0
- 添加TrustZone支援
- QoS管理功能
- 多協議支援

## 🆘 支援與聯繫

- 問題回報: GitHub Issues
- 文檔: `docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf`
- 範例: `examples/` 目錄

## 📄 許可證

本專案採用BSD-2-Clause許可證 - 詳見LICENSE文件。

---

**注意**: 此工具生成的RTL代碼已經過綜合驗證，可用於FPGA和ASIC實現。VIP環境支援主流模擬器(VCS、Questa、Xcelium)。