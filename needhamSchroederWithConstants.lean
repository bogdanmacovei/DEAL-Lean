-- language -- 
inductive message (σ : ℕ) : Type 
  | null : fin σ -> message 
  | conc : message -> message -> message 
  | nonc : message -> message 
  | keys : message -> message -> message -> message 
  | encr : message -> message -> message
  | decr : message -> message -> message
  | tupl : message -> message -> message 
  | func : message -> message -> message 

-- notation `<` m `>` k := message.encr m k 
-- notation m1 `||` m2 := message.conc m1 m2 

inductive program (σ : ℕ) : Type 
  | skip : program 
  | secv : program -> program -> program 
  | reun : program -> program -> program 
  | send : program 
  | recv : program 

inductive form (σ : ℕ) : Type 
  | atom : fin σ -> form 
  | botm : form 
  | impl : form -> form -> form 
  | k : message σ -> form -> form 
  | b : message σ -> form -> form 
  | pdl : program σ -> message σ → message σ → form -> form 
  | mesg : message σ -> form 

prefix `#` := form.atom 
notation `⊥` := form.botm
infix `⊃` := form.impl 
notation `~`:40 p := form.impl p ⊥ 
notation p `&` q := ~(p ⊃ ~q)
notation p `or` q := ~(~p & ~q)
notation `K□`:80 m `,` p := form.k m p 
notation `B□`:80 m `,` p := form.b m p 
notation `[` α ` : ` i ` , ` j ` ] `:80  p := form.pdl α i j p 
notation `c` m := form.mesg m 

/-
  Context definition 
-/

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

notation `·` := {}
notation Γ ` ∪ ` p := set.insert p Γ


/-
  Proof system 
-/

open form 
open message
open program 

inductive Proof (σ : ℕ) : ctx σ → form σ → Prop 
-- Propositional logic
| ax { Γ } { p : form σ } (h : p ∈ Γ) : Proof Γ p  
| pl1 { Γ } { p q : form σ } : Proof Γ (p ⊃ (q ⊃ p))
| pl2 { Γ } { p q r : form σ } : Proof Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 { Γ } { p q } : Proof Γ (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
-- S5
| kk { Γ } { i : message σ } { p q } : Proof Γ (K□ i, (p ⊃ q) ⊃ (K□ i, p ⊃ K□ i, q))
| t { Γ } { i : message σ } { p } : Proof Γ ((K□ i, p) ⊃ p) 
| s4 { Γ } { i : message σ } { p } : Proof Γ (K□ i, p ⊃ K□ i, K□ i, p) 
-- KD
| bk { Γ } { i : message σ } { p q } : Proof Γ (B□ i, (p ⊃ q) ⊃ (B□ i, p ⊃ B□ i, q))
| dox { Γ } { i : message σ } { p } : Proof Γ (B□ i, p ⊃ ~B□ i, (~p))
| kb { Γ } { i : message σ } { p } : Proof Γ (K□ i, p ⊃ B□ i, p)
-- PDL
| pdlk { Γ } { i j : message σ } { p q } (α : program σ) : Proof Γ ([α : i, j](p ⊃ q) ⊃ ([α : i, j]p  ⊃ [α : i, j] q))
-- Deductive rules 
| mp { Γ } { p q } (hpq: Proof Γ (p ⊃ q)) (hp : Proof Γ p) : Proof Γ q
| knec { Γ } { i : message σ } { p } (h : Proof · p) : Proof Γ (K□ i, p)
| bnec { Γ } { p } { i : message σ } (h : Proof · p) : Proof Γ (B□ i, p)
| gen { Γ } { p } { i j : message σ } (α : program σ) (h : Proof · p) : Proof Γ ([α : i, j]p)
-- Constant deduction system 
| c₁ { Γ } { t k : message σ } (h₁ : Proof Γ $ c t) (h₂ : Proof Γ $ c k) : Proof Γ (c t.encr k) 
| c₂ { Γ } { t k : message σ } (h₁ : Proof Γ $ c t.encr k) (h₂ : Proof Γ $ c k) : Proof Γ $ c t 
| c₃ { Γ } { t₁ t₂ : message σ } (h₁ : Proof Γ $ c t₁) (h₂ : Proof Γ $ c t₂) : Proof Γ $ c func t₁ t₂ 
-- Protocols 
| h00 { Γ } { p : form σ } { i j : message σ } 
    (hsend : Proof Γ [send : i , j] p) 
    : Proof Γ [recv : j, i] p 
| h01 { Γ } { p : form σ } { i j : message σ } 
    (hsend : Proof Γ [recv : i , j] p) 
    : Proof Γ [send : j, i] p 
| h1 { Γ } { p : form σ } { i j : message σ } { α : program σ } 
    (ha : Proof Γ [α : i, j]p) 
    : Proof Γ (K□ i, p) 
| h2 { Γ } { p : form σ } { k i j : message σ } 
    (h₀ : Proof Γ $ B□ i, (c k.keys i j)) 
    (h₁ : Proof Γ $ [recv : i, j]p) 
    : Proof Γ $ K□ i, B□ j, c k.keys i j 
| h3 { Γ } { k i j S : message σ }
    (h₀ : Proof Γ $ K□ i, c k)
    (h₁ : Proof Γ $ K□ j, c k)
    (h₂ : Proof Γ $ K□ S, c k)
    : Proof Γ $ c k.keys i j 


notation Γ `-` σ ` ⊢κ ` p := Proof σ Γ p
notation Γ `-` σ ` ⊬κ ` p := Proof σ Γ p → false 

/-
  Modeling Needham-Schroeder 
-/

open Proof 

variable σ : ℕ 
variables { A B S : message σ }
variables { Na Nb Kab Kas Kbs : message σ }
variable Γ : ctx σ 


axiom A_init_knowledge_0 : Γ-σ ⊢κ K□ A, c Na 
axiom A_init_knowledge_1 : Γ-σ ⊢κ K□ A, c Kas
axiom B_init_knowledge_0 : Γ-σ ⊢κ K□ B, c Nb 
axiom B_init_knowledge_1 : Γ-σ ⊢κ K□ B, c Kbs 
axiom S_init_knowledge_0 : Γ-σ ⊢κ K□ S, c Kas
axiom S_init_knowledge_1 : Γ-σ ⊢κ K□ S, c Kbs
axiom S_init_knowledge_2 : Γ-σ ⊢κ K□ S, c Kab

axiom A_to_S_0 : Γ-σ ⊢κ [send : A, S] c Na 
axiom S_to_A_1_0 : Γ-σ ⊢κ [send : S, A] c Na.encr Kas 
axiom S_to_A_1_1 : Γ-σ ⊢κ [send : S, A] c Kab.encr Kas 
axiom S_to_A_1_2 : Γ-σ ⊢κ [send : S, A] c ((Kab).encr Kbs).encr Kas 
axiom A_assumption_2 : Γ-σ ⊢κ B□ A, c Kab.keys A B
axiom A_to_B_3 : Γ-σ ⊢κ [send : A, B] c ((Kab).encr Kbs).encr Kas 
axiom B_assumption_3 : Γ-σ ⊢κ B□ B, c Kab.keys A B
axiom B_to_A_4 : Γ-σ ⊢κ [send : B, A] c Nb.encr Kab 

axiom OSS_A_init_knowledge_0 : Γ-σ ⊢κ K□ A, c Na 
axiom OSS_A_init_knowledge_1 : Γ-σ ⊢κ K□ A, c Kab 
axiom OSS_B_init_knowledge_0 : Γ-σ ⊢κ K□ B, c Kab 

axiom OSS_A_to_B : Γ-σ ⊢κ [send : A, B] c Na.encr Kab 

theorem B_knows_Na : ∅-σ ⊢κ K□ B, c Na := 
  have h₀ : ∅-σ ⊢κ [recv : B, A] c Na.encr Kab,
    from h00 $ @OSS_A_to_B σ A B Na Kab ∅,
  have h₁ : ∅-σ ⊢κ K□ B, c Na.encr Kab,
    from h1 h₀,
  have h₂ : ∅-σ ⊢κ c Na.encr Kab,
    from mp t h₁,
  have h₃ : ∅-σ ⊢κ c Kab,
    from mp t $ @OSS_B_init_knowledge_0 σ B Kab ∅,
  have h₄ : ∅-σ ⊢κ c Na,
    from c₂ h₂ h₃,
  show ∅-σ ⊢κ K□ B, c Na,
    from knec h₄ 

  theorem OSS_B_knows_Na : ∅-σ ⊢κ K□ B, c Na :=
    knec $ c₂ (mp t $ h1 $ h00 $ @OSS_A_to_B σ A B Na Kab ∅) 
    (mp t $ @OSS_B_init_knowledge_0 σ B Kab ∅)

  

theorem A_knows_B_believes_Kab_term : Γ-σ ⊢κ K□ A, B□ B, c Kab.keys A B := 
  have h₀  : Γ-σ ⊢κ B□ A, c Kab.keys A B,
    from @A_assumption_2 σ A B Kab Γ,
  have h₁  : Γ-σ ⊢κ [send : B, A] c Nb.encr Kab,
    from @B_to_A_4 σ A B Nb Kab Γ,
  have h₂  : Γ-σ ⊢κ [recv : A, B] c Nb.encr Kab,
    from h00 h₁,
  show Γ-σ ⊢κ K□ A, B□ B, c Kab.keys A B,
    from h2 h₀ h₂  

theorem A_knows_B_believes_Kab { A B Nb Kab : message σ } : Γ-σ ⊢κ K□ A, B□ B, c Kab.keys A B :=
begin 
  apply h2, 
  {
    exact @A_assumption_2 σ A B Kab Γ
  },
  {
    apply h00,
    {
      exact @B_to_A_4 σ A B Nb Kab Γ 
    }
  }
end 

lemma belief_over_conjunction { φ ψ : form σ } { A : message σ } 
  (h₁ : Γ-σ ⊢κ B□ A, φ) (h₂ : Γ-σ ⊢κ B□ A, ψ) :
  Γ-σ ⊢κ B□ A, (φ & ψ) := sorry  

theorem BAN_MMSK { A B m Kab : message σ } 
  (h₁ : Γ-σ ⊢κ K□ A, c Kab.keys A B)
  (h₂ : Γ-σ ⊢κ B□ A, [recv : A, B] c m.encr Kab) :
    Γ-σ ⊢κ B□ A, [send : B, A] c m :=
  sorry 
  


-- set_option trace.eqn_compiler.elim_match true


