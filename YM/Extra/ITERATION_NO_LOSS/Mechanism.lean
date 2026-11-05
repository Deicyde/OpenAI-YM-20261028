import YM.Extra.ITERATION_NO_LOSS.Gates

/-!
# Same-ticket propagation from cutoff to level zero

Uses `Inherited.*` at *every* period (not comparing interpolations off the
mesh in finite volume). Heat and new arrays must of course still have their
fresh-source hypotheses `Rates` proved on these clocks and actual functions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Tree Bloch Bid Craft Input Calibration Inherited
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {M : Horizon a} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}
    {Q : PostCost D} {O : ChartRatio G} (hc : Before S U A H K) (hw : Warm H W) (hp : Paid I a) (hm : M.Suffices K)
    (hg : GapQuote D K Q) (hO : LocalRatio O) (hB : ∀ N m : ℕ, m ≤ N → ∀ p, Sworn (M.H N m) (a.S.side m p) G)
    (hT : ∀ N m : ℕ, m < N → Harmonic (M.towers N m)) (hR : Rates M K U A H Q O)

structure Peak (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (N : ℕ) (T : PathData G) : Prop where
  ticket : Ticket M K U A N N T
  peak p : ∀ j, j ≤ 4 → SameJet j (main (n:=a.S.side N p) T (a.params N).clip) (Wilson.energy ∘ represent)
  initial b : (T.loop b).coeff = 0

structure Move (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (Q : PostCost D) (O : ChartRatio G)
    (N m : ℕ) (T R : PathData G) (ρ : Branch a m) (α : ℝ) : Prop where
  ticket : Ticket M K U A N m R
  shell : OnShell M Q N m T ρ
  kinetic : |α+G.slopeConstant*Real.log (a.S.block m).val|+1 ≤ (a.params (m+1)).drift
  classicalPart p F : ClassicalMatch (S:=a.clock.op m p) F (a.params (m+1)).clip (a.params m).clip T R (ρ p F)
  thermal p F : FiniteBound (S:=a.clock.op m p) F T R (a.params (m+1)).clip (a.params m).clip α O
    (ρ p F) (Q.Γ (a.clock.J (m+1))) (Q.c (a.clock.J (m+1))) (a.clock.loopCap (m+1))

include hc hp hm hB hR in
theorem peak (N : ℕ) : ∃ T, Peak M K U A N T := by
  obtain ⟨t,v,ht,hv,h1,h2,H⟩ := hR.initial N
  let R := bundle (M.H N N) t v (fun _ => blank G 2)
  have hk : A.top (a.clock.J N) ≤ A.cap U K (a.clock.J N) := (le_max_of_le_left (le_max_right ..) : _ ≤ A.price U K (a.clock.J N)).trans
    (le_mul_of_one_le_left ((zero_le_one' ℝ).trans (A.price_ge ..)) (by norm_num))
  have h0 := make_ticket hc hm hp.stage N N le_rfl R rfl (fun _ => blank_sym) ht hv blank_silent
    (Cost.enlarge (blank_cost _) ((zero_le_one' ℝ).trans (cap_loop_ge N))) (Cost.enlarge h1 hk) (Cost.enlarge h2 hk)
  refine ⟨R,h0,fun p j hj => ?_,fun i => rfl⟩
  have hl := top_lower (M.H N N) (K.η (a.clock.J N)) _ h0.funded (hm.all N N le_rfl _) h0.rooted.attached
    (hB N N le_rfl p) (hm.top N _)
  by_cases he : j ≤ 2
  · exact hl _ he
  exact ⟨main_jet h0.funded,(hl 0 (by omega)).2.1,H p j (by omega) hj⟩

include hp hw hm hB hg in
theorem select {N m : ℕ} (h : m<N) {T : PathData G} (ht : Ticket M K U A N (m+1) T) : ∃ ρ, OnShell M Q N m T ρ := by
  have H (p : ℕ) := hg.serves a M N m p (a.clock.J (m+1)) rfl (block_eq hp m).symm hp.kernel
    (larger hw hp m p) h hm (hB N (m+1) h p) T _ _ _ ht.funded ht.rooted.attached
  choose t ht using fun p F => (H p F).2
  exact ⟨t,fun p F => (H p F).1,fun p F => (ht p F).1,fun p F => (ht p F).2.1,fun p F => (ht p F).2.2⟩

abbrev glue (M : Horizon a) (N m) (T : PathData G) (e d l) := bundle (M.H N m) (join e (inherit M N m T.cubic))
    (join d (inherit M N m T.quartic)) (join l (inheritLoop M N m T.loop))

section resumes
variable {N m : ℕ} {T : PathData G} (hne : m<N) (ht : Ticket M K U A N (m+1) T)
local notation "j" => (a.clock.J (m+1))
local notation "k" => (a.clock.J m)
local notation "L" => (a.S.block m)
local notation "credit" => A.cap U K j
local notation "η" => U.clear K j k
local notation "σ" => Stage.width (a.params (m+1))

include hc hp hm ht hne hw hT
lemma resume {e d l} (hse : SymmetricAtoms e) (hsd : SymmetricAtoms d) (hsl : SymmetricAtoms l) (hz : Silent l)
    (h1 : Charged e (a.params m).width (rem3 (A.fresh j k) credit L))
    (h2 : Charged d (a.params m).width (rem4 (A.fresh j k) credit credit L))
    (h3 : Charged l (a.params m).width (H.det j k*((L).val:ℝ)^4)) : Ticket M K U A N m (glue M N m T e d l) := by
  have hv := provision hc hm hp N m hne
  have he := U.clear_pos K j k
  have hJ : 1 ≤ j-2 := by have := a.clock.adm (m+1); omega
  have hs := (a.params (m+1)).width_pos
  have hfit : η ≤ σ*(L).val := hv.early.fit.trans (by gcongr; linarith)
  have hC := classical_price hJ he hv.high hv.low hv.tower ht.cube (by decide) hfit
  have hD := classical_price hJ he hv.high hv.low hv.tower ht.quartic (by decide) hfit
  have hL := loop_price hJ he hv.high hv.low hv.tower ht.funded.two hv.early.fit
  let i := T.cubic; let q := T.quartic; let u := T.loop
  have si : SymmetricAtoms i := fun i => (ht.funded.invariant i).2.1
  have sq : SymmetricAtoms q := fun i => (ht.funded.invariant i).2.2
  have su : SymmetricAtoms u := fun i => (ht.funded.invariant i).1
  have pB := A.price_ge U K k
  have pA := A.price_covers U K j k (a.fits.mono (Nat.le_succ m)) (a.fits.stepSlow m)
  let b := A.price U K k; have hb : 0 ≤ b := (zero_le_one' ℝ).trans pB
  let r3 := credit/((L).val:ℝ)^2; let r4 := credit/((L).val:ℝ)^4
  have h : A.fresh j k ≤ b := (le_max_left ..).trans pA
  have hB := hv.early.amplitude
  change r3 ≤ 1 ∧ r4 ≤ 1 at hB
  have hr := A.cap_pos U K j
  have hfit3 := join_cost h1 (hC.mono hv.width le_rfl)
  have hfit4 := join_cost h2 (hD.mono hv.width le_rfl)
  refine make_ticket hc hm hp.stage N m hne.le _ rfl (join_sym hsl (loop_sym _ _ _ su)) (join_sym hse (classical_sym _ _ _ si))
    (join_sym hsd (classical_sym _ _ _ sq)) (join_silent hz (loop_silent hJ he hv.high hv.low hv.tower (a.S.block_odd m) (hT N m hne) ht.funded.two hv.early.fit))
    (Cost.enlarge (join_cost h3 (hL.mono hv.width le_rfl)) ?_) (Cost.enlarge hfit3 ?_) (Cost.enlarge hfit4 ?_)
  · have ht := hv.early.loop
    have hs : diffPrice η σ (K.Ω j) (K.Ω k) / ((L).val:ℝ)^2 ≤ 1/4 := (div_le_iff₀ (by have := side_pos L; positivity)).mpr (by linarith)
    have hcap := cap_loop_ge (a:=a) (m+1)
    linarith only [loop_ceiling hw hp m, mul_le_mul_of_nonneg_right hs ((zero_le_one' ℝ).trans hcap)]
  · calc
      _ = A.fresh j k*(1+r3) + carryPrice η (K.Ω j) (K.Ω k) 3 * r3 := by unfold r3 rem3; ring
      _ ≤ b*(1+1) + b*1 := add_le_add (mul_le_mul h (by linarith only [hB.1]) (by unfold r3; positivity) hb)
        (mul_le_mul ((le_max_of_le_right (le_max_left ..)).trans pA) hB.1 (by unfold r3; positivity) hb)
      _ ≤ _ := by change _ ≤ 6*b; linarith
  calc
    _ = A.fresh j k * (1+r3+r3^2+r4) + carryPrice η (K.Ω j) (K.Ω k) 4 * r4 := by unfold r4 r3 rem4; ring
    _ ≤ b*4+b*1 := add_le_add (mul_le_mul h (by nlinarith only [pow_le_pow_left₀ (by unfold r3; positivity) hB.1 2,hB.2,hB.1])
      (by unfold r3 r4; positivity) hb) (mul_le_mul ((le_max_of_le_right (le_max_right ..)).trans pA) hB.2 (by unfold r4; positivity) hb)
    _ ≤ _ := by change _ ≤ 6*b; linarith

include hR hB hg hO
lemma extend : ∃ (R : PathData G) (ρ : Branch a m) (α : ℝ), Move M K U A Q O N m T R ρ α := by
  obtain ⟨ρ,hρ⟩ := select hw hp hm hg hB hne ht
  obtain ⟨e,d,hse,hsd,h1,h2,hJu⟩ := hR.classicalPart N m T ρ hne ht hρ _ _ ht.cube ht.quartic
  obtain ⟨α,l,hsl,hzl,h3,hα,hJl⟩ := hR.quantum N m T ρ hne ht hρ
  let R := glue M N m T e d l
  have ht' : Ticket M K U A N m R := resume hc hw hp hm hT hne ht hse hsd hsl hzl h1 h2 h3
  have hv := provision hc hm hp N m hne
  have hJ : 1 ≤ j-2 := by have := a.clock.adm (m+1); omega
  have he := U.clear_pos K j k
  have hs := (a.params (m+1)).width_pos
  have hx := (a.params m).width_pos
  have hfit : η ≤ σ*(L).val := hv.early.fit.trans (by gcongr; linarith)
  have hC := (classical_price hJ he hv.high hv.low hv.tower ht.cube (by decide) hfit).mono hv.width le_rfl
  have hD := (classical_price hJ he hv.high hv.low hv.tower ht.quartic (by decide) hfit).mono hv.width le_rfl
  have hL := (loop_price hJ he hv.high hv.low hv.tower ht.funded.two hv.early.fit).mono hv.width le_rfl
  have Hu (p F) : ClassicalMatch (S:=a.clock.op m p) F (a.params (m+1)).clip (a.params m).clip T R (ρ p F) := by
    obtain ⟨H,e0,hH⟩ := hJu p
    let S := a.clock.op m p
    refine all_forests (larger hw hp m p) hO (hρ.critical p H) (hρ.critical p F) ht.funded ht'.funded (Q.price _) (hρ.gap _ H) (hρ.gap _ F) e0 (fun u hu => ?_)
    by_cases hi : u ≤ 2
    · exact lower (M.H N (m+1)) (M.H N m) (larger hw hp m p) ht.funded ht'.funded (hm.all N _ hne _)
        (hm.all N _ hne.le _) ht.rooted.attached ht'.rooted.attached (hB N (m+1) hne p) (hB N m hne.le p) (hρ.critical p H) (hρ.quadratic p H) e0 u hi
    have hv' := classical_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
      (hm.all N _ hne _) (hB N (m+1) hne p) (hm.crossings N m p hne) ht.cube (by decide) hfit (hρ.critical p H) (hρ.guessed p H) 3 le_rfl
    have hy := classical_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
      (hm.all N _ hne _) (hB N (m+1) hne p) (hm.crossings N m p hne) ht.quartic (by decide) hfit (hρ.critical p H) (hρ.guessed p H) 4 le_rfl
    exact higher T R ht'.funded rfl rfl h1 hC h2 hD (hρ.critical p H) ⟨hH.three,hH.four⟩ hv' hy u (by omega) hu
  refine ⟨R,ρ,α,ht',hρ,?_,Hu, fun p F => ?_⟩
  · unfold Levels.params Calendar.params; rw [hp.stage]; exact (add_le_add_left hα _).trans (hc.drift _ _ (a.fits.mono (Nat.le_succ m)) (a.fits.stepSlow m))
  obtain ⟨F0,e0,hH⟩ := hJl p
  let S := a.clock.op m p
  have hy := loop_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
    (hm.all N _ hne _) (hB N (m+1) hne p) (hm.crossings N m p hne) ht.funded.two (silent_of_bounds ht.funded) hv.early.fit (hρ.critical p F0) (hρ.guessed p F0) 2 le_rfl
  have hb := determinant_price T (Q.price j) (hρ.gap _ F0) (hρ.critical _ F0) e0 hO (M.H N m) _ _ _ _ ht'.funded h3 hL (Q.pos j).le (cap_loop_ge (a:=a) (m+1)) hH hy
  exact (transplant (a.blocks m p).branches (larger hw hp m p) hO (hρ.critical p F0) (hρ.critical p F) ht.funded ht'.funded (Q.price j)
    (hρ.gap p F0) (hρ.gap p F) e0 hb (fun u hu => Hu p F0 u hu e0)).1
end resumes
end YM.Extra.Iteration
