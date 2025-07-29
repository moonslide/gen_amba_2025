# 檔案整理計劃

## 目前問題分析
1. 太多重複的PDF產生器檔案
2. 過多的文檔報告檔案（*.md）
3. 測試檔案散佈在根目錄
4. 截圖檔案沒有統一管理
5. 備份檔案混在主要檔案中

## 建議的目錄結構

```
axi4_vip/gui/
├── README.md                              # 主要說明文檔
├── requirements.txt                       # Python依賴
├── launch_gui.sh                         # 主要啟動腳本
├── 
├── src/                                  # 核心程式碼
│   ├── bus_matrix_gui.py                # 主GUI應用程式
│   ├── axi_verilog_generator.py         # RTL產生器
│   ├── vip_environment_generator.py     # VIP產生器
│   └── ...（其他核心檔案）
│
├── docs/                                 # 文檔目錄
│   ├── AMBA_Bus_Matrix_Complete_User_Guide.pdf  # 最終用戶指南
│   ├── user_guide_generator/            # PDF產生器
│   │   ├── create_complete_guide.py     # 主要產生器
│   │   ├── sections/                    # 各章節實作
│   │   │   ├── rtl_section.py
│   │   │   ├── vip_section.py
│   │   │   └── ...
│   │   └── assets/                      # 圖片資源
│   │       ├── screenshots/             # GUI截圖
│   │       └── diagrams/               # 技術圖表
│   └── reports/                         # 開發報告（歸檔）
│
├── examples/                            # 使用範例
│   ├── README.md
│   ├── simple_system/
│   ├── automotive_soc/
│   └── datacenter_config/
│
├── templates/                           # 配置模板
│   ├── axi4_templates/
│   ├── ahb_templates/
│   └── mixed_protocol/
│
├── tests/                              # 測試檔案
│   ├── unit_tests/
│   ├── integration_tests/
│   └── test_data/
│
├── output/                             # 產生的檔案
│   ├── rtl/
│   ├── vip/
│   └── reports/
│
└── scripts/                           # 工具腳本
    ├── install_dependencies.sh
    ├── run_tests.sh
    └── cleanup.sh
```

## 清理動作
1. 移除重複的PDF產生器
2. 整理文檔到docs目錄
3. 移動測試檔案到tests目錄
4. 整理截圖到assets目錄
5. 清理臨時和備份檔案