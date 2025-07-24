AMBA AXI4 匯流排工具開發指南 (完整版)
前言
本指南詳細解析了實現一個健壯的 AXI4 匯流排工具所需滿足的核心要求。我們將深入探討協議的關鍵信號、功能邏輯以及事務處理機制，並提供具體的實現檢查點與開發建議。所有內容均嚴格參照 AMBA AXI and ACE Protocol Specification (ARM IHI 0022D) 文件。

第一部分：核心信號實現
1. AxPROT (保護類型信號)
規範要求：


AxPROT[2:0] (包含 ARPROT 和 AWPROT) 是一個 3 位信號，用於定義事務的存取權限 。從設備 (Slave) 必須能夠根據這些屬性來判斷一次存取是否合法。其編碼定義如下 ：




AxPROT[0]：定義特權等級。0 表示非特權 (Unprivileged) 存取，1 表示特權 (Privileged) 存取 。




AxPROT[1]：定義安全狀態。0 表示安全 (Secure) 存取，1 表示非安全 (Non-secure) 存取 。




AxPROT[2]：定義存取類型，作為提示 (Hint)。0 表示數據 (Data) 存取，1 表示指令 (Instruction) 存取 。


關鍵實現檢查點：

完整傳輸：您的工具（無論是 Master、Slave 還是 Interconnect 模型）是否能完整傳輸並接收 3 位的 AxPROT 信號？

Slave 存取控制：Slave 模型是否內建了存取控制邏輯？例如，當一個標記為「只讀」且「僅限特權」的地址空間收到一個「非特權寫入」請求時，Slave 是否能正確地拒絕該請求並返回 SLVERR 響應？

安全隔離：Interconnect 和 Slave 模型是否能根據 AxPROT[1] 的值實現安全與非安全世界的隔離？非安全事務是否無法存取被標記為安全的地址空間？


指令/數據提示：雖然是提示，但您的模型是否能正確傳遞 AxPROT[2] ？這對於連接需要區分指令和數據快取的處理器模型至關重要。

開發者建議：

在您的 Slave 模型中實現一個可配置的記憶體映射 (Memory Map)。該映射應允許用戶為不同地址區域定義不同的存取權限（讀寫權限、特權級、安全狀態）。

設計驗證測試案例，專門用於觸發各種權限錯誤，確保 Slave 和 Interconnect 能正確處理非法存取並生成對應的錯誤響應。

確保您的 Master 模型可以生成所有 AxPROT 的組合，以全面測試下游設備的反應。

2. QoS 相關信號 (AxQoS)
規範要求：
AXI4 協議引入了 

AWQOS 和 ARQOS 兩個 4 位信號，用於支持服務品質 (Quality of Service) 。規範建議將其用作事務的優先級指示器，數值越高代表優先級越高 。預設值 


0b0000 表示不參與任何 QoS 機制 。Interconnect 等組件應利用此信號進行仲裁，但 AXI 的排序規則（基於 ID）優先級高於 QoS 。


關鍵實現檢查點：

信號實現：您的 Master 和 Interconnect 模型是否包含了 4 位的 AxQoS 端口？


優先級仲裁：Interconnect 的仲裁邏輯是否會考慮 AxQoS 的值？在多個 Master 同時發起請求時，高 QoS 的事務是否會被優先處理 ？


排序規則優先級：驗證您的 Interconnect 在處理帶有相同 AXI ID 的事務時，是否仍然遵循 AXI 的順序性保證，即使這些事務的 QoS 值不同 。

預設值處理：當 Master 模型不驅動 AxQoS 時，其值是否正確地被視為 0b0000？

開發者建議：

在您的 Interconnect 模型中實現一個可配置的、基於 QoS 的加權輪詢 (Weighted Round-Robin) 或嚴格優先級 (Strict Priority) 仲裁器。

設計一個能夠動態調整 AxQoS 值的 Master 模型，以模擬不同流量優先級的場景（例如，影片串流 vs. 普通數據傳輸）。

在驗證環境中，使用計分板 (Scoreboard) 監控事務的延遲，驗證高 QoS 事務的平均延遲是否確實低於低 QoS 事務。

3. 區域標識信號 (AxREGION)
規範要求：


AWREGION 和 ARREGION 是 AXI4 規範中定義的可選 4 位信號 。它們的主要目的是允許一個物理上的 Slave 接口在系統地址映射中呈現為多達 16 個不同的邏輯接口 。Interconnect 根據高位地址的解碼結果生成 





AxREGION 值，並將其傳遞給 Slave 。這使得 Slave 無需自己執行複雜的地址解碼，就能區分事務是發往哪個邏輯區域（例如，控制寄存器區域或數據 FIFO 區域）。規範要求 



AxREGION 的值在任何 4KB 地址空間內必須保持不變 。

關鍵實現檢查點：

Interconnect 生成：您的 Interconnect 模型是否能根據系統的地址映射正確生成 AxREGION 值？

Slave 解析：您的 Slave 模型是否能解析 AxREGION，並根據其值將事務路由到不同的內部邏輯單元？


不支持的區域：當 Slave 收到一個它不支持的 AxREGION 值時，它如何反應？是返回錯誤響應，還是將其視為某個預設區域的別名 ？協議要求其必須以符合協議的方式完成事務，以防止死鎖。

4KB 邊界：驗證 AxREGION 在 4KB 地址範圍內是否保持恆定。

開發者建議：

對於需要實現多種功能模式的複雜 Slave，使用 AxREGION 可以簡化其內部設計。您可以將不同的功能塊（如配置、狀態、數據端口）映射到不同的 AxREGION 值。

在您的 Interconnect 模型中，實現一個可編程的地址映射表，用於定義從物理地址到 AxREGION 的轉換規則，從而提高系統配置的靈活性。

設計測試案例，向同一個 Slave 的物理地址範圍發送帶有不同 AxREGION 值的事務，以驗證該 Slave 是否能正確地區分並處理這些邏輯上的不同訪問。

4. 緩存屬性信號 (AxCACHE)
規範要求：


AxCACHE[3:0] 用於定義事務的記憶體屬性 。AXI4 相較於 AXI3 有重要更新。


Modifiable 屬性 (AxCACHE[1])：此位取代了 AXI3 的 "Cacheable" 位 。


0 (Non-modifiable)：事務不可被拆分或合併 。事務的地址、突發大小/長度/類型、鎖定類型等參數在傳輸過程中必須保持不變 。唯一的例外是，長度超過 16 的 INCR 突發可以被拆分成多個較短的突發 。




1 (Modifiable)：事務可以被 Interconnect 修改，例如拆分成多個事務、合併多個事務、預取比請求更多的數據，或寫入比請求更大的地址範圍（使用 WSTRB 控制）。


Bufferable 屬性 (AxCACHE[0])：當設置為 1 時，表示 Interconnect 或任何組件可以延遲事務到達其最終目的地 。對於寫事務，這意味著可以提前返回響應。

關鍵實現檢查點：

Non-modifiable 事務處理：您的 Interconnect 模型是否嚴格遵守 Non-modifiable 規則？它是否會錯誤地合併或拆分 AxCACHE[1]=0 的事務（除了 >16 的 INCR 突發）？

Modifiable 事務處理：您的 Interconnect 是否能正確處理 Modifiable 事務的優化？例如，將多個小的寫入合併成一個較大的突發。

Bufferable 寫入：對於 Bufferable 寫事務，您的 Interconnect 模型是否能提前發送寫響應 (BRESP)，而不是等待最終 Slave 的確認？

開發者建議：

創建兩套驗證序列：一套生成 Non-modifiable 事務，另一套生成 Modifiable 事務。

在驗證環境中，設計一個檢查器 (Checker) 來監控 Non-modifiable 事務的屬性，確保其從 Master 發出到抵達 Slave 的過程中保持不變。

測試您的 Slave 模型是否能處理被 Interconnect 合併或拆分後的 Modifiable 事務。

第二部分：功能邏輯實現
1. 獨占訪問 (Exclusive Accesses)
規範要求：
AXI4 透過 1 位的 

AxLOCK 信號和 EXOKAY 響應來支持獨占訪問（旗標型操作）。


過程：Master 首先發起一個獨占讀 (ARLOCK=1)，Slave 記錄該地址和 ARID 。之後，Master 發起一個獨占寫 (

AWLOCK=1) 到相同地址，且 AWID 必須與 ARID 匹配 。

響應：

如果從獨占讀到獨占寫期間，沒有其他 Master 寫入過該位置，則獨占寫成功，Slave 更新記憶體並返回 

EXOKAY 響應 (BRESP=0b01) 。


如果已有其他 Master 寫入，則獨占寫失敗，記憶體不被更新，Slave 返回 

OKAY 響應 (BRESP=0b00) 。



限制：獨占訪問的突發大小和長度必須一致，地址必須對齊到事務總字節數，總傳輸字節數必須是 2 的冪（最大 128 字節），且突發長度不超過 16 。

關鍵實現檢查點：


監控邏輯：您的 Slave 模型是否實現了獨占訪問監控器 (Exclusive Access Monitor)？它能否為每個 AXI ID 記錄一個獨占地址 ？


成功/失敗路徑：

測試成功路徑：獨占讀 -> 獨占寫，驗證返回 EXOKAY。

測試失敗路徑：獨占讀 (Master A) -> 普通寫 (Master B) -> 獨占寫 (Master A)，驗證 Master A 的獨占寫返回 OKAY 且數據未被寫入。

EXOKAY vs. OKAY：您的 Master 模型是否能正確解讀 EXOKAY 和 OKAY 響應，並在失敗時執行重試邏輯？

限制檢查：您的工具是否會對不符合限制（如地址不對齊、突發長度不匹配）的獨占訪問發出警告或錯誤？

開發者建議：

實現一個多 Master 的驗證環境，以模擬真實世界中多個處理器核心競爭同一旗標的場景。

在您的 Slave 監控器中加入日誌功能，詳細記錄獨占讀的地址、ID，以及導致獨占狀態被清除的寫操作，便於調試。

2. 響應信號完整性 (RRESP/BRESP)
規範要求：
讀響應 (

RRESP[1:0]) 和寫響應 (BRESP[1:0]) 提供 4 種事務狀態 ：


0b00 (OKAY)：表示正常訪問成功，或獨占寫失敗 。




0b01 (EXOKAY)：表示獨占訪問成功 。




0b10 (SLVERR)：從設備錯誤。表示訪問成功到達 Slave，但 Slave 內部發生錯誤（例如，寫入只讀寄存器、FIFO 溢出）。




0b11 (DECERR)：解碼錯誤。通常由 Interconnect 產生，表示目標地址不存在對應的 Slave 。


關鍵實現檢查點：

四種響應生成：您的 Slave 和 Interconnect 模型是否能生成所有四種響應？

錯誤觸發：

能否透過存取一個未映射的地址來觸發 DECERR？

能否透過對 Slave 模型中的特定地址進行非法操作（如寫保護）來觸發 SLVERR？

Master 處理：您的 Master 模型是否能正確處理 SLVERR 和 DECERR？例如，觸發中斷或進入錯誤處理程序。


響應傳遞：對於讀突發，Slave 是否可以在突發的不同傳輸中返回不同的響應（例如，部分 OKAY，部分 SLVERR）？對於寫突發，是否只在整個突發結束後返回一次響應 ？


開發者建議：

實現一個「預設 Slave」(Default Slave)，用於回應所有未映射地址的訪問。該 Slave 應始終返回 

DECERR 響應 。這有助於捕獲系統中的地址錯誤。

在您的驗證環境中，使用錯誤注入 (Error Injection) 技術隨機觸發 SLVERR 和 DECERR，以測試系統的容錯能力。

3. 突發傳輸與地址計算
規範要求：
AXI4 對突發傳輸有明確規定：


突發長度 (AxLEN)：Burst_Length = AXLEN[7:0] + 1 。對於 

INCR 突發類型，AXI4 支持 1 到 256 次傳輸 。對於 

WRAP 和 FIXED 類型，長度限制為 1 到 16 次傳輸 。


回繞突發 (WRAP)：長度必須是 2、4、8 或 16 。地址在到達回繞邊界時會折返 。回繞邊界的計算公式為：


Wrap_Boundary = (INT(Start_Address / (Number_Bytes * Burst_Length))) * (Number_Bytes * Burst_Length) 。


4KB 邊界：任何突發都不能跨越 4KB 的地址邊界 。

關鍵實現檢查點：

INCR 長度：您的 Master 模型是否能生成長達 256 次傳輸的 INCR 突發？您的 Slave 和 Interconnect 是否能正確處理？

WRAP 地址計算：您的地址生成器是否能為 WRAP 突發計算正確的回繞邊界和後續地址？

4KB 邊界檢查：您的 Master 模型和驗證環境是否會檢查並防止生成跨越 4KB 邊界的突發？Interconnect 或 Slave 在收到此類非法突發時應如何反應（例如，返回錯誤）？


FIXED 突發：地址是否在整個突發過程中保持不變 ？

開發者建議：

編寫一個專門的地址計算函數庫，該庫包含 INCR、FIXED 和 WRAP 三種突發類型的地址生成邏輯，並對其進行單元測試。

創建針對性的測試案例，覆蓋 WRAP 突發的各種邊界條件，例如起始地址正好是回繞邊界，或起始地址接近邊界。

使用斷言 (Assertion) 來自動檢查是否有任何突發跨越了 4KB 邊界。

4. 低功耗接口信號
規範要求：
這是一組

可選的接口信號，用於協調 Master/Slave 與系統時鐘控制器之間的低功耗狀態轉換 。


CSYSREQ：由時鐘控制器發出，請求外設進入或退出低功耗狀態 。


CSYSACK：由外設發出，確認已收到 CSYSREQ 請求 。


CACTIVE：由外設發出，指示其是否需要時鐘 。

協議定義了進入和退出低功耗狀態的完整握手時序 。

關鍵實現檢查點：

信號支持：您的工具模型（特別是 Slave）是否提供了這些可選的低功耗端口？

握手時序：如果實現了該功能，Slave 的狀態機是否能正確響應 CSYSREQ 的變化，並在適當的時機驅動 CACTIVE 和 CSYSACK？


拒絕請求：Slave 是否能透過保持 CACTIVE 為高電平來拒絕進入低功耗狀態的請求 ？

開發者建議：

由於這是可選功能，建議在您的工具模型中將其作為一個可配置的選項。

如果您的目標是設計需要低功耗管理的 SoC，建議實現一個時鐘控制器的行為模型，以便在驗證環境中驅動這些低功耗信號，測試您的 DUT。

第三部分：事務處理機制
1. 事務排序 (基於 AXI ID)
規範要求：
AXI4 的排序模型基於 ARID 和 AWID。


相同 ID：來自同一 Master、具有相同 ID 的事務有嚴格的排序保證 。

對於設備記憶體 (Device Memory)，所有事務必須按照發出順序抵達 Slave 。

對於普通記憶體 (Normal Memory)，訪問相同或重疊地址的事務必須按發出順序抵達 Slave 。

讀響應和寫響應也必須按發出順序返回給 Master 。


不同 ID：來自同一 Master 但具有不同 ID 的事務之間沒有排序保證，可以亂序完成 。


讀寫依賴：讀通道和寫通道是獨立的 。如果 Master 需要保證一個寫操作在一個讀操作之後發生，它必須等待讀操作的響應 (

RLAST) 到達後，才能發出寫操作 。

關鍵實現檢查點：

ID 追蹤：您的 Interconnect 和 Slave 模型是否能追蹤每個事務的 ID？

順序性保證：

測試相同 ID 的多個寫入到同一地址，驗證它們是按順序被 Slave 接收的。

測試相同 ID 的多個讀取，驗證讀數據是按順序返回的。

亂序處理：測試不同 ID 的多個事務，驗證它們可以被亂序處理（例如，後發的請求先完成）。

讀寫屏障：驗證您的 Master 模型是否能正確實現讀寫屏障邏輯（等待響應）。

開發者建議：

在您的驗證平台中，實現一個能夠追蹤所有在途事務 (in-flight transactions) 及其 ID 的計分板。該計分板應包含檢查器，用於自動驗證 AXI 排序規則是否被遵守。

設計一個高性能 Master 模型，該模型能夠發出多個具有不同 ID 的亂序請求，以充分測試 Interconnect 和 Slave 的處理能力。

2. 用戶自定義信號 (AxUSER)
規範要求：
AXI4 在每個通道上都提供了

可選的用戶自定義信號 (AWUSER, ARUSER, WUSER, RUSER, BUSER) 。協議本身不定義這些信號的用途，它們完全由用戶定義，可以用於傳輸側帶信息，如數據校驗、調試標識等 。信號的寬度由實現者定義，且每個通道可以不同 。



關鍵實現檢查點：

接口提供：您的工具模型是否提供了 AxUSER 端口？


信號直通：Interconnect 模型是否能將 AxUSER 信號從 Master 透明地傳遞到 Slave，反之亦然，而不做任何修改 ？

寬度匹配：您的工具在連接不同 AxUSER 寬度的組件時，是否有合理的處理機制（例如，報錯、截斷或擴展）？

開發者建議：

即使您的設計當前不需要 AxUSER，也建議在您的 Interconnect 模型中實現這些信號的直通邏輯。這將為未來的系統擴展和集成第三方 IP 提供靈活性。

如果您的工具需要使用 AxUSER，請務必為其用途編寫詳細的文檔，以避免在系統集成時出現誤解。
