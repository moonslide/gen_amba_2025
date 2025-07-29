#\!/bin/bash
# AMBA Bus Matrix GUI啟動腳本

# 檢查當前目錄
if [ \! -f "src/bus_matrix_gui.py" ]; then
    echo "錯誤: 請在axi4_vip/gui目錄下執行此腳本"
    exit 1
fi

# 檢查Python依賴
echo "檢查Python依賴..."
python3 -c "import tkinter; print('✓ tkinter')" 2>/dev/null || (echo "✗ tkinter未安裝" && exit 1)
python3 -c "import matplotlib; print('✓ matplotlib')" 2>/dev/null || (echo "✗ matplotlib未安裝" && exit 1)
python3 -c "import numpy; print('✓ numpy')" 2>/dev/null || (echo "✗ numpy未安裝" && exit 1)

echo "所有依賴已安裝，啟動GUI..."

# 啟動GUI
cd "$(dirname "$0")/.."  # 回到gui目錄
python3 src/bus_matrix_gui.py "$@"
EOF < /dev/null
