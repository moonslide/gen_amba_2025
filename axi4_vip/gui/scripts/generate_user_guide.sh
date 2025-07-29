#\!/bin/bash
# 產生完整用戶指南PDF

echo "正在產生AMBA Bus Matrix完整用戶指南..."

cd "$(dirname "$0")/../docs/user_guide_generator"

if [ \! -f "create_complete_guide.py" ]; then
    echo "錯誤: 找不到PDF產生器"
    exit 1
fi

python3 create_complete_guide.py

if [ $? -eq 0 ]; then
    echo "✅ 用戶指南產生成功！"
    echo "📄 檔案位置: docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf"
else
    echo "❌ 用戶指南產生失敗"
    exit 1
fi
EOF < /dev/null
