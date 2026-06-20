# GPXuploader

スマホブラウザで使うための Streamlit Cloud 公開用パッケージです。

## 中身

- app.py  
  GPXuploader本体
- requirements.txt  
  Streamlit Cloudで必要なPythonライブラリ一覧
- .streamlit/config.toml  
  画面テーマ・アップロード上限などの設定

## 使い方

1. GitHubで新しいリポジトリを作る
2. このフォルダ内の `app.py`, `requirements.txt`, `.streamlit/config.toml` をアップロードする
3. Streamlit Community Cloudでリポジトリを選択する
4. Main file path に `app.py` を指定してデプロイする
5. 発行されたURLをスマホで開く
6. ChromeまたはSafariでホーム画面に追加する

## 注意

- この版はスマホブラウザ利用向けです。
- GPX生成、マンション画像取得、Excel指定マンション画像取得、住所順、チラシ合成ロジックはv198のままです。
- 3:4化や夜化などの自然画像編集はChatGPT側で個別に行う運用です。
- Google Street View自動取得は有料API前提になるため、現時点では含めていません。
