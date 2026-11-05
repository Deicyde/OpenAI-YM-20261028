import YM.RG08.Door.Setup
/-!
# Preloan explicit mesh expenses. All fixed *before* increasing lengths.
Including as-needed lease post-block.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall PowerSeries Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {κ : KernelChoices}{G : Gauge} {i k d t r e j D τ E:ℕ} {F : Labels.Frame G d}{T:SectionData F}(H:Hol G) {R w v A B Z C:ℝ} {P:KPrices κ}{K:Lending G κ}{g:KGate P}

abbrev expQ (F:Labels.Frame G d)(Z:ℝ): ℝ:=1+(Fintype.card (Letter F):ℝ)*Z
lemma expQ_pos (F:Labels.Frame G d)(h:0≤Z): 1≤ expQ F Z:=le_add_of_nonneg_right (by positivity)
-- Head/E; Lease money before X; stage J; sort menu.
structure Signals (K0:KPrices κ)(P:Lending G κ)(E τ:ℕ)(H:Hol G)(T:SectionData F)(h:1/2≤R)(ht:d+1≤D) where
  wi : ℕ→ℝ
  vi : ℕ→ℝ
  cost : ℕ→ℕ→ℝ
  gate : ℕ→ℕ
  pos i : 0<wi i
  ores i : snug τ E (windows τ E) • wi i ≤ vi i
  arcs i : funding E (windows τ E) • vi i ≤ ticketW P i
  rose i : wi i≤ K0.b i
  admits i j : 1≤cost i j
  pad i j (X:Flight j i) : 4 ≤ i → d+2 ≤ j → gate j ≤ X.L.val → vi i ≤ X.L.val*(wi j / ((τ+E+1:ℕ):ℝ))
  pros i j (X:Flight j i) : 4 ≤ i → d+2≤j → gate j ≤ X.L.val → ∀ r≤τ+E,∀ V:EnvelopeU D R G r, Polished V→ Abates V (d+1)→∀ C:ℝ, Quire.Lit V (wi j) C → Quire.Lit (aboard d (eff κ X G) V) (wi i) (C /Real.sqrt X.L.val / (expQ F (cost j i)))
  posts i j (X:Flight j i) : 4 ≤ i → d+2 ≤ j→ ∀ U:Session (Letter F),Flash X.L U→(∀ b v:Letter F,slot b=slot v→ hot U 0 v b=leadingV H T (d.le_succ.trans ht) h X κ.penalty b v)→∀ b v:Letter F,‖diagonalSl (hot U⁻¹ 0) b v‖≤cost j i

-- no maximal growth calls included
lemma orient (P:KPrices κ)(K:Lending G κ)(τ E:ℕ)(h:1/2≤R)(hp:d+1≤D)(hS:T.Sound H)(hB:Bid.pop T): Nonempty (Signals P K E τ H T h hp) := by
  let a:= ((snug τ E (windows τ E)):ℝ)
  let c:= ((funding E (windows τ E)):ℝ)
  have hs : 0<c:= by unfold c funding; positivity
  have hA: 0<a:= by unfold a; exact_mod_cast (snug_p (τ:=τ) (e:=E) (i:=windows τ E))
  let v i:= ticketW K i/c; have he i:0<v i:=div_pos (ticket_pos ..) hs
  let w i:=min (P.b i) (v i/a); have hx i: 0<w i:=lt_min (P.positive _) (div_pos (he _) hA)
  choose A hA' hr using fun i j=> billsSl (i:=i) (j:=j) (K:=κ) H hS hB h hp
  choose V hV using fun i j r=> manExp h hp (hx j) (hx i) (P:=P) (min_le_left ..) (G:=G) (j:=j) (hz:=expQ_pos F (zero_le_one.trans (hA' i j))) r
  let Q j:= w j / ((τ+E+1:ℕ):ℝ); have ht j:0<Q j:=div_pos (hx j) (by positivity)
  choose W hW using fun i j=> exists_nat_gt (v i/Q j)
  let A' i j:= ((range (τ+E+1)).sup (V i j)); let B i j:=max (A' i j) (W i j)
  let X j:= max (B j j) (B (j-1) j)
  have hQ i j (M:Flight j i): B i j ≤ X j:= by
    unfold X; by_cases h:i=j
    · rw [h]; exact le_max_left ..
    rw [show j-1=i by have hx:=M.mono; have hh:=M.narrow; omega]; exact le_max_right ..
  refine ⟨⟨w,v,(fun i j=> A j i),X,hx,fun i=> ?_,fun i=>?_,fun i=>min_le_left ..,fun i j=> hA' j i,?_,?_,hr⟩⟩
  · rw [nsmul_eq_mul]; change a*w i≤ v i; rw [mul_comm]; exact (le_div_iff₀ hA).1 (min_le_right ..)
  · rw [nsmul_eq_mul]; change c*(ticketW K i/c) ≤ ticketW K i; rw [mul_div_cancel₀ _ hs.ne']
  · intro i j M hi hj hp; exact (div_le_iff₀ (ht j)).1 ((hW i j).le.trans (by exact_mod_cast (le_max_right ..).trans ((hQ i j M).trans hp)))
  intro i j M hi hj hp r hu; exact hV i j r M hi hj ((le_sup (b:=r) (s:=range (τ+E+1)) (f:=V i j) (by simp; omega)).trans ((le_max_left ..).trans ((hQ i j M).trans hp)))

end YM.RG08.Door
