import Mathlib

/- 命题逻辑的形式化 -/

/- 语法定义 -/
inductive PropForm : Type
  | var : Nat → PropForm                    -- 命题变量，用Nat表示
  | neg : PropForm → PropForm               -- 否定
  | impl : PropForm → PropForm → PropForm   -- 蕴含
  deriving Countable, Encodable

open PropForm

-- 定义逻辑运算符的符号
prefix:5 "⇁" => PropForm.neg
infixr:8 " ⟶ " => PropForm.impl
infixl:7 " ⩒ " => fun p q => (⇁p) ⟶ q                    -- 析取
infixl:6 " ⩑ " => fun p q => ⇁(p ⟶ (⇁q))                 -- 合取
infixl:9 " ⟷ " => fun p q => (p ⟶ q) ⩑ (q ⟶ p)          -- 等价
