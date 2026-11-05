import YM.Extra.MULTISOURCE_TRAJECTORIES.Sublayers
import YM.Extra.SOURCE_HISTORIES.Tickets
import YM.Extra.WILSON_STARTUP.MixRoom
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Believe
import YM.Further.ITERATION_RECIPE_PRODUCER.Both
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Coupons
/-!
# Determinant budget at the real Course output (whole density terminal)

Need exact physical end root, all marker slots incl orientations. Can't use rebate
as-is since Uses & Settled on Lawful not obtained for auxiliary V. Use genuine P
estimate, pay fee on *per-site* scalar by comparison to whitespace R; doesn't discard any
sign or volume power. White itself not assumed to be on a Course. Export same Root test
at same budgets. Rest of Array calculation as in Next/RANK/Stamp,Allowance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Set Filter RG Lattice Wilson Cells Next.Rank Marker Glyph Exponential MeasureTheory Station
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal
variable {G : Gauge} {n : Side}
section size
variable {P : Rep G n} (O : HaarBudget G) {σ δ s Λ w : ℝ} (h : Tissue P σ s Λ δ w)
    {X g z : ℝ}
local notation "K"=> Fintype.card (Site n)
include h
lemma denture (hn :∀ U,0 ≤ P.eval U) (hL : 1 < n.val) (hg : 0<g) (hp : g ≤ P.p.threshold) (hβ:P.beta*g^2=1)
    (F : Config G n→ℂ) (hI : Integrable F (prior G n)) (hz : 0≤z) (hQ : ∀ U,z*‖F U‖≤ Real.exp (P.exponent U+(K:ℝ)*X)) :
    z* ‖∫ U,F U ∂prior G n‖ / (∫ U,P.eval U∂prior G n) ≤ Real.exp ((K:ℝ)*protection O P s Λ δ X g-4*G.lieDim*Real.log g):= by
  let Y:= white P; let A:= prior G n; let R:=(K:ℝ)*δ
  have ht U:0 ≤ Y.eval U:= by unfold Y; rw [whiteEval]; exact mul_nonneg (Real.exp_pos _).le (hn _)
  have hv U : -R ≤ P.exponent U-Y.exponent U ∧ P.exponent U-Y.exponent U≤R:= abs_le.mp (e_volume P h.patch U).2
  have hf : 0<∫ U,Y.eval U∂A:=
    lt_of_lt_of_le (by have hp:= O.positive; positivity) (vacuum_bound h.status O ht hg hp hβ)
  have hP : (∫ U,Y.eval U∂A) ≤ Real.exp R * ∫ U,P.eval U∂A:= by
    rw [← integral_const_mul]; refine integral_mono ((Y.envelope h.status).integrable _) ((payEnv P h).integrable _|>.const_mul _) ?_
    intro i; change (white P).eval i ≤ _; rw [whiteEval]; have he := (hv i).1; rw [whiteExp] at he
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by unfold Y at he; linarith only [he])) (hn _)
  have hY :0<∫ U,P.eval U∂A:= pos_of_mul_pos_right (hf.trans_le hP) (Real.exp_pos _).le
  have hw := determinant h.status O ht hL hg hp hβ F hI hz (X:=X+δ) (fun U=> (hQ U).trans (Real.exp_monotone ?_))
  swap; unfold R Y at hv; linarith only [(hv U).2]
  rw [div_le_iff₀ hY]; refine ((div_le_iff₀ hf).1 hw).trans ((mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le).trans_eq ?_)
  rw [← mul_assoc,← Real.exp_add]; unfold R protection Rep.exCost; simp only [white]; ring_nf
end size
section stamp
open Next.Rank.Array
variable {V : Type} [Fintype V] [DecidableEq V] {F : Family G} {N p m k : ℕ} {T : Tiling (F.side N p)}
variable {X : Config G (F.side N p) → veil V} (c : Course F N p k) (hm : m≤N)
theorem s_postage (o : HaarBudget G) {P : Rep G (F.side m p)} (hp : c.Uses m hm P)
    {σ A Λ δ ν g : ℝ} (hP : Tissue P σ A Λ δ ν)
    (hg : 0<g) (he : g≤P.p.threshold) (hβ : P.beta*g^2=1)
    (tz : Fintype.card T.Cell = Fintype.card (Site (F.side m p)))
    {r e l L : ℝ} (hr : 0<r) (eu : 0 ≤ e)
    (h : ∀ i : modes V,Continuous fun U => (X U).part i)
    {ζ : T.Cell×V → Site (F.side m p)}
    (H : Value.Notice P ζ (c.flow (Next.Rank.Array.stamp T (F.beta N p) X) m hm) (fun _ => r) e l L) (s : modes V) :
    T.rootTest (F.beta N p) (fun U => (X U).part s) ≤
      Real.exp (protection o P A Λ δ (L+(Fintype.card V:ℝ)*l) g-4*G.lieDim*Real.log g / (Fintype.card T.Cell:ℝ)) / r^s.val.card := by
  let q := Fintype.card T.Cell
  have hq : 0<q := T.cells_positive
  let b := F.beta N p
  let S := Glyph.allCells T.Cell s
  let Y := c.flow (Next.Rank.Array.stamp T b X) m hm
  have hi := hP
  have hu : (∫ U,P.eval U∂prior G _) = Wilson.partition G (F.side N p) b := hp.density ▸ c.vacuum_total hm
  have hpos : ∀ U,0 ≤ P.eval U := hp.density ▸ c.vacuum_lower hm
  have ht : 1 < (F.side m p).val := by
    exact lt_of_lt_of_le (by norm_num : 1 < 4) (Nat.le_of_dvd (F.side m p).property (F.S.side_four m p))
  have hd := denture o hi hpos ht hg he hβ (fun U => (Y U).part S) (by
    exact (Poly.get S).integrable_comp (c.flow_int _ ((stamped_cont T b h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ..))
    (show 0 ≤ Poly.toll (fun _ => r) S from (Poly.worth (fun _ => hr) _).le) (X:=L+(Fintype.card V:ℝ)*l) (fun U => by
      refine (Poly.member (fun _ => hr) _ _).trans ((H.price (fun _ => hr) eu U).trans_eq ?_);congr 1
      rw [Fintype.card_prod, tz]; push_cast; ring)
  let C := protection o P A Λ δ (L+(Fintype.card V:ℝ)*l) g
  let pN := Wilson.partition G (F.side N p) b
  have ha : 0<pN := partition_pos _
  have H' : (r^s.val.card)^q * ‖moment b (fun U => ∏ i : T.Cell,T.copy i (fun u => (X u).part s) U)‖ ≤ Real.exp (q*C-4*G.lieDim*Real.log g) := by
    dsimp only [Y] at hd
    rw [flow_credit _ _ T s h, hu,norm_mul,Complex.norm_real,Real.norm_of_nonneg ha.le,← tz,Glyph.all_price s r] at hd
    apply le_trans _ hd; apply le_of_eq; symm; apply (div_eq_iff ha.ne').2; dsimp only [pN,q,b]; ring
  apply YM.Stock.spacer _ _ _ q (norm_nonneg _) (pow_pos hr s.val.card) hq
  rw [mul_comm]; apply H'.trans_eq; congr 1; dsimp only [C]
  have hx : 0 < (q:ℝ) := by exact_mod_cast hq
  change (q:ℝ)*_ -_=_*(_-_/q)
  field_simp
end stamp
section rebate
open Next.Rank.Ship Next.Rank.Read
variable {C : Family G} {N p k M n: ℕ} {x : Points n} {b : ℝ}
theorem coupon (O : HaarBudget G) (hc : Allocated C.path.levels M k O b) (hb : bank O C.path.levels (width C.path.levels b k))
    {P : Rep G (C.side (width C.path.levels b k) p)} {u : Course C N p k} {hN : k ≤ N} {q : width C.path.levels b k ≤ N}
    (hp : Ferm P u q) (t : Fin n → C.book.Token)
    (B : Fin n → (standard C).Tag) (hx : Fit C.path.levels b k x) (hn : n ≤ M)
    {e c d : ℝ} (he : 0 ≤ e) (hE : c≤1) (hC : d ≤ 1) (hv : estimate P u hN x (invoice B t hx N p) e c d (allowance C.path.levels M k))
    (s : modes (Fin n)) (sh : s.val.Nonempty) :
    let T := yard C b hN p
    T.rootTest (C.beta N p) (fun U => (invoice B t hx N p U).part s) ≤ budget C.path.levels M k := by
  intro T
  let A:= C.path.levels; let r:= width A b k
  obtain ⟨H,σ,g,Λ,δ,w,hD,hd⟩ := hp
  have hea := s_postage (X:=invoice B t hx N p) (T:=T) u q O H hd hD.positive hD.entrance hD.assigned rfl (Real.exp_pos _) he (bill_cont _ _ hx N p) hv s
  have hc1 := hc.permitted.plateau r le_rfl ((wider A b k).trans (before A b k))
  have hQ : A.params r=A.params k := congr_arg A.clock.stage hc1
  let Z := Fintype.card (Site (A.S.side r p))
  rw [Fintype.card_fin, show Fintype.card T.Cell=Z from rfl] at hea
  have hs : d+n*c ≤ 1+(M:ℝ) := by
    refine add_le_add hC ((mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _ : 0 ≤ (n:ℝ))).trans ?_)
    rw [mul_one]; exact_mod_cast hn
  let I := pot A M k
  have hi : protection O P (A.params r).paths Λ δ (d+n*c) g - 4*G.lieDim*Real.log g/(Z:ℝ) ≤ I := by
    apply (hb p P g Λ δ (d+n*c) M hD hs).trans
    change ticket O (A.params r) M ≤ I; rw [hQ]; exact hc.charge
  apply hea.trans
  let a := allowance A M k
  have ha : 1 ≤ a := fixed ..
  calc
    _ ≤ Real.exp I / a^s.val.card := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hi) (pow_nonneg (zero_le_one.trans ha) _)
    _ ≤ Real.exp I / a := by
      gcongr
      calc
        a = a^1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ ha (Finset.card_pos.mpr sh)
    _ = _ := by change Real.exp I / Real.exp (2*I)=Real.exp (-I); rw [← Real.exp_sub]; congr 1; ring
end rebate
end YM.PhysicalNext.InteractingRank.Soft
