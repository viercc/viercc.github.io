---
title: ネットワークのトラブルシューティング
---

（自宅のネットワーク環境でトラブったのでメモ代わりにここに記録します）

## 現象

* 自宅のネットワーク機器のうち、Ubuntu 20.04をインストールしていた2台のPCだけが、30~60分で通信できなくなった。
  * Ubuntu 20.04の機器はこの2台以外にはなかった。
  * クリーンインストールしても発生した
  * Windows10とデュアルブートしていた機器では、Windows10を動作させているときにこの現象はなかった

* 自宅のインターネット回線は[auひかり ちゅら](https://www.au.com/okinawa_cellular/hikari/)であり、借りているHGW(AtermBL900HW)にWifiまたは有線のEthernetで接続していた
  * Wifiでも有線でも、この現象は必ず発生した
* 通信できなくなる直接の原因は、PCが（HGWから）DHCPで配布してもらっていたIPv4アドレスの更新に失敗するため
  * 切断→再接続で復帰していた
  * パケットをキャプチャしたところ、この現象が発生していたPCでもHGW上のDHCPサーバからDHCPACKパケットを受信できていた ⇒ DHCPクライアントの問題が想定できる
  
## 解決方法

* Ubuntu20.04(デスクトップ向け)のネットワーク関係の設定は、デフォルトの状態では、[NetworkManager](http://manpages.ubuntu.com/manpages/focal/man8/NetworkManager.8.html)デーモンが管理している。以下、「デフォルトでは」は省略する。
* NetworkManagerは、DHCPクライアントとしてNetworkManagerに組み込みのDHCPクライアント機能を使用する。
* 組み込みのDHCPクライアント機能に代わって、[dhclient](http://manpages.ubuntu.com/manpages/focal/en/man8/dhclient.8.html)を使用するように設定すると、この現象は発生しなくなった。
  * 設定には、`/etc/NetworkManager/NetworkManager.conf`に次の行を追加した。

    ```
    [main]
    plugins=ifupdown,keyfile
    # この行を追加した
    dhcp=dhclient

    [ifupdown]
    managed=false
    ```

  * 組み込みのDHCPクライアント機能でこの現象が発生した理由は不明
    * 以下推測
      * このHGWは、同一MACアドレスからの頻繁な`DHCPREQUEST/DISCOVER`に対して、ある一定以下の頻度(15〜30分程度)でしか`DHCPACK/OFFER`を返さない
        * まあ理解できる
      * 組み込みのDHCPクライアントは、DHCPサーバからの応答を待つ時間・応答がない場合にリクエストを再送するまでの時間ともに短い
        * 理解できる
        * しかしその設定を変更する方法がわからない。NetworkManagerを自分でコンパイルする以外無理？
      * 組み込みのDHCPクライアントは、大多数の`DHCPREQUEST`が無視される環境で機能しない
        * なんで？？？？？？？？
