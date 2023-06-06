module libs.Maybe where
  data Maybe {n} (A : Set n) : Set n where
    nothing : Maybe A
    just    : A → Maybe A