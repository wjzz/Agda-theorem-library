-- @author : Wojciech Jedynak (wjedynak@gmail.com)
-- @date   : 2011-12-29
-- @tags   : agda; stdlib; prelude
-- @short  : Commonly used Agda modules. Imported so that different modules won't interfere.

module Prelude where

-- programming types

open import Data.Bool  public hiding (_≟_; decSetoid)
import Data.Fin        renaming (zero to fzero; suc to fsuc)
open   Data.Fin        public using (Fin; fzero; fsuc)
open import Data.List  public using (List;[];_∷_;map;_++_;reverse)
open import Data.Maybe public hiding (decSetoid; setoid)
open import Data.Nat   public hiding (_≟_)
import Data.Vec renaming (map to vmap; _++_ to vapp; reverse to vreverse)
open   Data.Vec public 
open import Function

-- logical types

open import Data.Empty   public 
open import Data.Product public hiding (map;zip)
open import Data.Sum     public hiding (map)
open import Data.Unit    public using (⊤)

-- proofs

open import Relation.Binary                       public
open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Relation.Nullary                      public

-- classes

open import Class.DecEq public


-- my modules

--import Data.List.Theorems
import Data.Nat.Theorems
--import Data.Vec.Theorems

-- these modules take too long to load

--import Data.Char        
--import Data.String

-------------
--  Tests  --
-------------

x : ℕ
x = 123

test : ℕ → ℕ
test n = if true then n else zero
