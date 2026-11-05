import YM.Bid.Scope
import YM.Next.STATIONARY.Level.Transition



set_option autoImplicit false
/-!
# Delayed open for the carried amplitude. Theta chosen after Rolls.
Proof permits repeated J=J, invariant with no curvature-cost escalation.
Contraction with Λ/2 wing for one-step postage.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}

lemma bump (k θ D : ℝ) (hk : 0≤k) (h : 0<θ) : ∀ᶠ s : ℝ in atTop,
    D ≤ 2*(Real.exp ((Real.log (Real.log s))^2))^θ ∧ (Real.exp ((Real.log (Real.log (s+k)))^2))^θ ≤ 2*(Real.exp ((Real.log (Real.log s))^2))^θ := by
  have hr : Tendsto (fun s:ℝ=> Real.log (Real.log s)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hp : Tendsto (fun s:ℝ=> Real.exp (Real.log (Real.log s)^2*θ)) atTop atTop := Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (show 2≠0 by decide)).comp hr |>.atTop_mul_const h)
  have hx := (hp.const_mul_atTop (show (0:ℝ)<2 by norm_num)).eventually_ge_atTop D
  have hv : Tendsto (fun x : ℝ => k/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hT : Tendsto (fun x : ℝ => 3*(k/x)*θ) atTop (𝓝 0) := by simpa using (hv.const_mul 3).mul_const θ
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),eventually_gt_atTop (1:ℝ),hv.eventually (ge_mem_nhds zero_lt_one),hx,hT.eventually (ge_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))] with v hl he hw hV hW
  have he₀ : 0<v := zero_lt_one.trans he
  let L:= Real.log v
  let H:= Real.log (v+k)
  have h0 : 0<L := Real.log_pos he
  have h1 : L≤H := Real.log_le_log he₀ (le_add_of_nonneg_right hk)
  have h2 : H ≤ L+k/v := by
    unfold H; rw [show v+k=v*(1+k/v) by field_simp, Real.log_mul he₀.ne' (by positivity)]
    exact add_le_add_right ((Real.log_le_sub_one_of_pos (by positivity : 0<1+k/v)).trans_eq (by ring)) _
  have hy : Real.log L ≤ Real.log H := Real.log_le_log h0 h1; have hz : 0 ≤ Real.log L := Real.log_nonneg hl
  have hu : Real.log H-Real.log L ≤ k/v/L := by
    rw [← Real.log_div (h0.trans_le h1).ne' h0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (h0.trans_le h1) h0)).trans ?_
    rw [sub_le_iff_le_add, div_add_one h0.ne']; exact div_le_div_of_nonneg_right (by linarith) h0.le
  have hH : Real.log H ≤ L+1 := ((Real.log_le_sub_one_of_pos (h0.trans_le h1)).trans (by linarith : H-1 ≤ _))
  have ht : Real.log L ≤ L := (Real.log_le_sub_one_of_pos h0).trans (by linarith)
  have hu : (Real.log H)^2-(Real.log L)^2 ≤ 3*(k/v) := by
    rw [sq_sub_sq]; calc
      _ ≤ (3*L)*(k/v/L) := by exact mul_le_mul (by linarith) hu (sub_nonneg.mpr hy) (by positivity)
      _ = _ := by field_simp
  rw [← Real.exp_mul, ← Real.exp_mul]; constructor
  · exact hV
  calc
    Real.exp _ ≤ Real.exp (Real.log 2+Real.log L ^2*θ) := Real.exp_monotone (by nlinarith only [hu,hW,h])
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num)]

lemma clocks (G : Gauge) (h : G.Simple) (s : Sheet G) (L : Rolls s) (Θ : Protection L) (W : ℕ → ℝ) :
    ∃ Δ : ℕ → ℝ, ∀ (D : Delays Θ) (T : Bar D) (V : Wait T), Δ≤ D.betaEntry → ∀ a : Levels G,Paid V a → ∀ m,
     let j := a.clock.J (m+1); W j ≤ a.clock.loopCap m ∧ a.clock.loopCap (m+1)/2 ≤ a.clock.loopCap m ∧ 1 ≤ a.clock.loopCap m := by
  let v i := G.slopeConstant * Real.log (L.L i).val
  have hv i : 0 ≤ v i := mul_nonneg (Gauge.slopeConstant_pos h).le (Real.log_nonneg (by exact_mod_cast Nat.succ_le_iff.mpr (L.L i).pos))
  choose w hw using fun i => eventually_atTop.1 (bump (v i) (Θ.theta i) (W i) (hv i) (Θ.pos i))
  refine ⟨w,fun D T V hp a H m => ?_⟩
  let s := a.clock.hatBeta m; intro j
  obtain ⟨ht,hk⟩ := hw j s ((hp j).trans (H.pays _))
  let E:= a.clock
  have hθ : E.theta j=Θ.theta j := congr_fun H.theta j
  have hx : a.clock.theta j≤ a.clock.theta (a.clock.J m) := a.fits.thetaMono (a.fits.mono (Nat.le_succ _))
  have hy := (a.fits.thetaRange m).1
  have hm : (1:ℝ) ≤ a.clock.monitor m := Real.one_le_exp (by apply sq_nonneg)
  have hg : 1 ≤ (a.clock.monitor m)^(a.clock.theta (a.clock.J m)) := Real.one_le_rpow hm hy.le
  have hL : (a.clock.monitor m)^(Θ.theta j)≤ (a.clock.monitor m)^(a.clock.theta (a.clock.J m)) := Real.rpow_le_rpow_of_exponent_le hm (hθ ▸ hx)
  have he : s+v j=a.clock.hatBeta (m+1) := by
    have hf : (L.L j)=a.clock.schedule.block m := (congr_fun H.lengths _).symm.trans (a.fits.sameFactor _)
    unfold s v; rw [hf,Calendar.hatBeta, Calendar.hatBeta, Schedule.scale_succ]; ring
  unfold Calendar.loopCap
  refine ⟨ht.trans (mul_le_mul_of_nonneg_left hL (by positivity)), ?_,by linarith only [hg]⟩
  rw [show a.clock.J (m+1)=j from rfl, show a.clock.theta j=_ from hθ,_root_.mul_comm 2, mul_div_cancel_right₀ _ (by norm_num)]
  apply le_trans _ (mul_le_mul_of_nonneg_left hL (by positivity))
  rw [he] at hk; exact hk
end YM.Stationary
end

/-!
# Fees ordered at same and both neighbors. Higher-index entries (future)
can appear in widths at level j; independence permits simultaneous demand.
Clip enlargement does not change earlier width/profiles other than what consumer
explicitly prices. Paces proof requires true Ramp provided separately. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}

def pacesE (K : MapPrices) (i : ℕ) := max 0 (K.Ω i)
lemma paces_pos (K : MapPrices) (i : ℕ) : 0≤pacesE K i := le_max_left ..
lemma paces_extend (K : MapPrices) (i : ℕ) : K.Ω i≤ pacesE K i := le_max_right ..

def BasesFine (G : Gauge) (P : MapPrices) (Z : ℕ→ℝ) (w A : ℕ→ℝ) := ∀ j,
    ∀ m : ℕ→Side, Tendsto (fun i=>(m i).val) atTop atTop → ∀ (p : Clip), p.direct ≤ Z j →
    ∀ (B : Bed), B.roots.strip (P.α j) (pacesE P j) → (∀ i, Floor B p i (P.η j) (pacesE P j)) →
      (∀ i,Bid.Sworn B (m i) G) → (∀ i, B.diagonal.acts (m i)=1) →
      ∃ R : PathData G,R.row=rowPath B ∧ Attached B R ∧
        (∀ i, (R.loop i).coeff=0) ∧ (∀ s a D, 0<s → s ≤ w j → A j ≤ a → 0 ≤ D → R.Bounds p s a D) ∧
       ∀ i n', n' ≤4 → SameJet n' (fun x => mainTerm p R (represent (x:fieldDir G (m i) 1))) (fun x => Wilson.energy (represent x))

theorem beckon (G : Gauge) (P : MapPrices) (Z : ℕ→ℝ) (he : ∀ i, 0≤Z i) : ∃ σ A : ℕ →ℝ,(∀ i, 0< σ i) ∧ (∀ i, 0≤A i) ∧ BasesFine G P Z σ A := by
  choose s a hs hS ha H using fun i => launch G (P.α i) (pacesE P i) (Z i) (P.alpha_pos i) (he i)
  refine ⟨s,fun i=> max (a i) (rowPrice (P.α i) (pacesE P i)),hs,fun i=> (ha i).trans (le_max_left ..),fun i m hm p hp B h hv hx hg=> ?_⟩
  obtain ⟨R,h1,h2,h3,h4,h5⟩ := H i m hm p B (P.η i) (pacesE P i) hp h hv hx hg
  exact ⟨R,h1,h2,h3,fun τ a Λ ht hb ha he=> h4 τ a _ ht hb ((le_max_left ..).trans ha) ((le_max_right ..).trans ha) he, h5⟩

lemma Transition.preserves {Z W V X Y J Z' A D C s σ d α k C' d' u v g g' U U'} (h : Transition G J k Z W V X Y Z' A D C C' d s g u U U') (hp : σ≤s) (hv : C' ≤ α) (he : d≤d') (ht : u ≤ v) (hz : g' ≤ g) {B B' : Side → ℝ} (hc : U≤ B) (hd : U'≤B') : Transition G J k Z W V X Y Z' A D C α d' σ g' v B B' := by
  intro m n P H p q R F M Gx Gy GK b r c l hk hL hm hu hQ S hB hC hE
  obtain ⟨T,w,h1,h2,h3,h4,h5,h6⟩ := h m n P H p q R F M Gx Gy GK b r c l hk (ht.trans hL) hm hu hQ S hB hC hE
  exact ⟨T,w,h1,h2,fun s v w he hh hu hg hl=>h3 s v w he (hh.trans hp) (hv.trans hu) ((hd _).trans hg) hl,h4.trans he,h5,fun i j hp hx=> h6 i j ((hc _).trans hp) (hx.trans hz)⟩

structure Proceed (G : Gauge) (P : MapPrices) (K : KernelChoices) (Z s A τ a d γ : ℕ →ℝ) (u : ℕ→ℕ) (F W : ℕ → Side → ℝ) : Prop where
    moon (j i : ℕ) (h : j=i ∨ j=i+1) : Transition G K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α i) (pacesE P i) (Z i) (a j) (τ j) (A i) (d j) (s i) (γ j) (u j) (F j) (W j)

def Fluent (G : Gauge) := ∀ (σ ε C Z τ A : ℝ),0<σ→0<ε→0≤C→0≤Z→0<τ→0≤A→ HorizCalc G σ ε C Z τ A

lemma colorAvail (G : Gauge) (h : G.Simple) : Nonempty G.ColorIndex := by
  by_contra! he; haveI : IsEmpty G.ColorIndex := he
  haveI := Gauge.Simple.nontrivial_color h
  obtain ⟨x,y,hx⟩ := exists_pair_ne G.Color; exact hx (by ext i; exact isEmptyElim i)

theorem claiming (G : Gauge) (hG : G.Simple) (K : KernelChoices) (P : MapPrices) (Z : ℕ→ℝ) (hZ : ∀ i,0 ≤ Z i) : ∃ s A : ℕ→ℝ,(∀ i,0<s i) ∧ (∀ i,0≤A i) ∧ BasesFine G P Z s A ∧
    ∀ (τ C : ℕ→ℝ), (∀ i, 0<τ i) → (∀ i,0 ≤ C i) → Fluent G →
       ∃ (d γ : ℕ →ℝ) (u : ℕ→ℕ) (F W : ℕ→ Side→ℝ),(∀ i, 0≤d i ∧ 0< γ i) ∧ Proceed G P K Z s A τ C d γ u F W := by
  obtain ⟨b,E,H,H',H₀⟩ := beckon G P Z hZ
  obtain ⟨i⟩ := colorAvail G hG
  choose v w hv hw I using fun (j r : ℕ) => transition_cap G i hG K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α r) (pacesE P r) (Z r) (P.eta_pos j) (P.alpha_pos j) (paces_pos P j) (hZ j) (P.alpha_pos r) (paces_pos P r) (hZ r)
  let s (i) := min (b i) (min (w i i) (w (i+1) i))
  let A (i) := max (E i) (max (v i i) (v (i+1) i))
  have hx i j (h : j=i ∨ j=i+1) : s i ≤ w j i ∧ v j i ≤ A i := by
    obtain rfl|rfl := h; exact ⟨(min_le_right ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_right ..)⟩; exact ⟨(min_le_right ..).trans (min_le_right ..), (le_max_right ..).trans (le_max_right ..)⟩
  refine ⟨s,A,fun i=>lt_min (H i) (lt_min (hw ..) (hw ..)),fun i=>(H' i).trans (le_max_left ..),?_,fun τ C hτ hC Y=>?_⟩
  · intro j m hm p hp B h hc hS he; obtain ⟨R,h₁,h₂,h₃,h₄,h₅⟩ := H₀ j m hm p hp B h hc hS he
    exact ⟨R,h₁,h₂,h₃,fun σ a Λ hu hs hf hg=> h₄ σ a Λ hu (hs.trans (min_le_left ..)) ((le_max_left ..).trans hf) hg, h₅⟩
  choose d c hd' F W hd hc h using fun (j i : ℕ) => I j i (τ j) (C j) (hτ j) (hC j) (Y _ _ _ _ _ _ (P.alpha_pos _) (P.eta_pos _) (paces_pos ..) (hZ _) (hτ _) (hC _))
  refine ⟨fun i=>max (d i i) (d i (i-1)),fun i=> min (c i i) (c i (i-1)),fun i=> max (hd' i i) (hd' i (i-1)),fun i x => max (F i i x) (F i (i-1) x),fun i x => max (W i i x) (W i (i-1) x),fun i=> ⟨(hd i i).trans (le_max_left ..),lt_min (hc i i) (hc i (i-1))⟩,?_⟩
  refine ⟨fun i j he=> Transition.preserves (h i j) (hx j i he).1 (hx j i he).2 ?_ ?_ ?_ ?_ ?_⟩
  all_goals
    rcases he with rfl|rfl <;> first
    | exact le_max_left ..
    | exact min_le_left ..
    | exact fun j=> le_max_left ..
    | (simp only [Nat.add_sub_cancel]; first|exact le_max_right ..| exact min_le_right ..| exact fun j=> le_max_right .. )
end YM.Stationary
end

/-!
# Carry PathData up to its peak. Fixed-clock retargeting only on A,T;
others of stack may be pinned knowing later requirements. Consumer uses
post tickets with labels preserved.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}

section story
variable {P : MapPrices} {K V : Horizon a} (Z : ChartRatio G)

structure SatPath (V : Horizon a) (N m : ℕ) (R : PathData G) : Prop where
  row : R.row=rowPath (V.H N m)
  ties : Attached (V.H N m) R
  bound : R.Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m)

def BranchRow (V : Horizon a) (N : ℕ) (R : PathData G) := SatPath V N N R ∧ (∀ p j,j ≤ 4 → SameJet j (fun x => mainTerm (a.params N).clip R (represent (x:fieldDir G (a.S.side N p) 1))) (fun x => Wilson.energy (represent x))) ∧ ∀ b,(R.loop b).coeff=0
abbrev GainWire (a : Levels G) (m : ℕ) := ∀ p : ℕ,(F : Forest (a.clock.op m p).ratio)→ fieldDir G (a.S.side m p) 1→AxisChart G F

-- Scales m-level. Need invariant B paths.
structure Bubble (V : Horizon a) (Q : PostCost L) (Z : ChartRatio G) (N m : ℕ) (R T : PathData G) (α : ℝ) (ρ : GainWire a m) : Prop where
    earns : |α + G.slopeConstant*Real.log (a.S.block m).val| + 1 ≤ (a.params (m+1)).drift
    lives : SatPath V N m T
    steps p (F : Forest (a.clock.op m p).ratio) :
        PriceGap F (a.params (m+1)).clip R (Q.η (a.clock.J (m+1))) ∧
        Critical F (a.params (m+1)).clip R (ρ _ F) ∧ Guessed F (installed (a.clock.op m p).ratio (V.towers N m).A0) (ρ _ F) ∧
        ClassicalMatch F (a.params (m+1)).clip (a.params m).clip R T (ρ p F) ∧ FiniteBound F R T (a.params (m+1)).clip (a.params m).clip α Z
            (ρ p F) (Q.Γ (a.clock.J (m+1))) (Q.c (a.clock.J (m+1))) 1

variable (h : Craft.Rack a P K) (he : Bid.Retained V K)
include h he
lemma hull_fact {m N : ℕ} (hm : m≤N) :
    Hull (V.H N m) (P.η (a.clock.J m)) (P.α (a.clock.J m)) (pacesE P (a.clock.J m)) (a.params m).clip (a.S.side m) G := by
  let i := a.clock.J m
  rw [he.1]; have hp := h.traces N m
  obtain ⟨-,h1,-,h3,h4⟩ := h.covers N m hm
  have hx := paces_extend P i
  refine ⟨fun i j=> (h1 i j).mono le_rfl hx,fun i j=> (h3 i j).mono le_rfl hx,fun n=> ?_,fun _=> h.oath N m _ hm⟩
  have hn := hp hm n
  have he (x : Co n (TypeFace 2) → ℝ) : 0 ≤ dotProduct x x := sum_nonneg (fun j _=> mul_self_nonneg _)
  exact { hn with uniform := ⟨fun i => ⟨(hn.uniform.1 i).1,(hn.uniform.1 i).2.trans (mul_le_mul_of_nonneg_right hx (he i))⟩,fun i=> ⟨(hn.uniform.2 i).1,(hn.uniform.2 i).2.trans (mul_le_mul_of_nonneg_right hx (he i))⟩⟩ }
lemma tack_columns {m N : ℕ} (hm : m<N) :
    let P':=(a.clock.op m 0).patch
    let i := a.clock.J (m+1)
    Headers (P:=P') (V.towers N m).A0 2 (P.α i) (pacesE P i) ∧ ∀ p,Towers.Diagonal (a.clock.op m p) (V.H N (m+1)) (V.H N m) (V.towers N m) := by
  intro X i
  obtain ⟨H,H'⟩ := he.2 N m hm
  refine ⟨?_,fun p=>?_⟩
  · have hk := a.clock.adm (m+1)
    change Headers (P:=X) _ _ _ _
    intro l hl; rw [H]
    have hx := (h.legs N m hm l (by omega)).1; exact fun p q=> (hx p q).mono le_rfl (div_le_div_of_nonneg_right (paces_extend _ _) (by positivity))
  rw [he.1]
  obtain ⟨h1,h2,h3⟩ := h.crosses N m p hm
  constructor
  · rw [H]; exact h1
  · rw [H']; exact h2
  rw [H,H']; exact h3
omit h he
lemma bound_climb (G : Gauge) (a : Levels G) (m : ℕ) : Tendsto (fun i => (a.S.side m i).val) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) a.S.period_strict.tendsto_atTop
  exact Nat.le_mul_of_pos_right _ (a.S.denominator m).property
end story

section apply
variable {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y}
    (h : Paid w a) (hg : ∀ i, GateVolume i ≤ W.shells i) {s₀ A C : ℕ→ℝ}
    (hx : (fun i => (s.profile i).width) ≤ s₀) (hC : C ≤ fun i => (s.profile i).paths)
    (hA : (fun i => (s.profile i).clip.direct)≤A) (hp : Craft.Rack a P K) (hk : Bid.Retained V K)
include hx hC hA h hp hk
lemma budding (B : BasesFine G P A s₀ C) (hu : ∀ m, 1 ≤ a.clock.loopCap m) (N : ℕ) : ∃ R : PathData G,BranchRow V N R := by
  let i:=a.clock.J N
  have H := hull_fact hp hk (m:=N) (le_refl N)
  have hh : a.params N=s.profile i := by unfold Levels.params Calendar.params; rw [h.stage]
  obtain ⟨R,h1,h2,h3,h4,h5⟩ := B i (a.S.side N) (bound_climb G a N) (a.params N).clip (hh ▸ hA i) (V.H N N) H.2.1 H.2.2.1 H.2.2.2 (fun n=> by rw [hk.1]; exact hp.top ..)
  exact ⟨R,⟨h1,h2,h4 _ _ _ (a.params _).width_pos (hh ▸ hx i) (hh ▸ hC i) (le_trans zero_le_one (hu N))⟩,h5,h3⟩
end apply
end YM.Stationary
end

/-!
# The transition butterfly. Supplies **all F** even outside eventually-start;
no period selection. Still parameterized: requires the stamps
 generated from leases on kinetic. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}

section cost
lemma higher_bill {c f : Side} {S : StepData c f} {F : Forest S.ratio} {R T : PathData G} {p q : Clip} {α A A' g y Λ Λ' : ℝ}
    {ρ : fieldDir G c 1→AxisChart G F} (h : FiniteBound F R T p q α Z ρ A g Λ) (hx : A*Λ*Real.exp (-g*c.val) ≤ A'*Λ'*Real.exp (-y*c.val)) : FiniteBound F R T p q α Z ρ A' y Λ' := by
  refine { h with wave_price := fun t i j σ τ hu he => ?_ }; apply (h.wave_price t i j σ τ hu he).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx (show 0≤(Fintype.card (Site c):ℝ) by positivity)
end cost
section level
variable {Zc A σ d g : ℕ → ℝ} {u : ℕ → ℕ} {F T : ℕ → Side → ℝ} {m N : ℕ}
variable (h : Paid w a) (hΘ : BudgetGap s L P Q.η) (hS : ∀ i, GateVolume i ≤ W.shells i) (ht : ∀ i (n : Side),W.shells i ≤ n.val → F i (L.L i)*Real.exp (-(g i)*n.val) ≤ Q.Γ i*Real.exp (-Q.c i*n.val))
variable (hi : (fun i=> (s.profile i).clip.direct) ≤ Zc) (hw : (fun i=> (s.profile i).width) ≤ σ) (hA : A ≤ fun i => (s.profile i).paths)
    (hq : d ≤ fun i => (s.profile i).drift) (hp : u≤ s.floorL) (he : LocalRatio Z)
    (hb : Craft.Rack a P K) (hk : Bid.Retained V K) (hJ : Proceed G P s.kernel Zc σ A (fun i=> (s.profile i).width) (fun i=> (s.profile i).paths) d g u F T)
include h hΘ hS ht hi hw hA hq hp he hb hk hJ
lemma energized (H : ∀ m,let j := a.clock.J (m+1); T j (L.L j) ≤ a.clock.loopCap m ∧ a.clock.loopCap (m+1)/2 ≤ a.clock.loopCap m ∧ 1 ≤ a.clock.loopCap m) {R : PathData G} (hy : R.Bounds (a.params (m+1)).clip (a.params (m+1)).width (a.params (m+1)).paths (a.clock.loopCap (m+1))) (hu' : Attached (V.H N (m+1)) R) (hm : m < N) :
    ∃ D α ρ,Bubble V Q Z N m R D α ρ := by
  let i:= a.clock.J m; let j:= a.clock.J (m+1); let U := a.params (m+1); let T' := a.params m
  let C := a.clock; let M:= (a.clock.op m 0).patch
  let p:= V.towers N m; let b := V.H N m; let z := V.H N (m+1)
  have hj : M.L=L.L j := (a.fits.sameFactor m).symm.trans (congr_fun h.lengths _)
  have h' : j=i ∨ j=i+1 := by
    have h : i≤j := a.fits.mono (Nat.le_succ m); have hi : j≤ i+1 := a.fits.stepSlow m; omega
  have hu : U=s.profile j := by unfold U Levels.params Calendar.params; rw [h.stage]
  have hT : T'=s.profile i := by unfold T' Levels.params Calendar.params; rw [h.stage]
  have hg v := larger h hS m v
  have hF := hull_fact hb hk hm; have hT' := hull_fact hb hk (le_of_lt hm)
  obtain ⟨h2,Ld⟩ := tack_columns hb hk hm
  let f := fun t => a.S.side m t; let c := fun t=> a.S.side (m+1) t
  have hv t (F : Forest (a.clock.op m t).ratio) := hΘ.ask j (a.clock.op m t) h.kernel hj rfl (hg t) F z b U.clip T'.clip R U.width U.paths _ _ _ _ p (Ld t) (hF.2.2.1 _) hy hu' (hF.2.2.2 t) (hT'.2.2.1 _)
  have hK t F := (hv t F).1
  choose ρ hρ using fun i F=> (hv i F).2
  let fF (t : ℕ) : Forest (a.clock.op m t).ratio := Classical.choice (Tree.select _ M.odd_side)
  let ξ : Armada f c M C.kernel := ⟨fun t=> (a.clock.op m t).sizes⟩
  let a' := fun i=> ρ i (fF i)
  have hZ : Transition G C.kernel j (P.η j) (P.α j) (pacesE P j) (Zc j) (P.α i) (pacesE P i) (Zc i) U.paths U.width (A i) (d j) (σ i) (g j) (u j) (F j) (T j) := by rw [hu,show C.kernel=s.kernel from h.kernel]; exact hJ.moon j i h'
  have hΦ : Scud ξ G U.clip T'.clip R fF a' (P.α j) U.width (pacesE P j) U.paths (pacesE P j) (P.η j) (a.clock.loopCap (m+1)) (P.α i) (pacesE P i) (P.η i) z b p (Q.η j) :=
      ⟨hg, hF,hT',hu',hy,h2,Ld,fun t=> hK t _,fun i=> (hρ i _).1,fun i=>(hρ i _).2.1, fun i=>(hρ i _).2.2⟩
  obtain ⟨Y,α,hX,hY,hP,hE,hG,H'⟩ := hZ f c M ξ U.clip T'.clip R fF a' z b p (a.clock.loopCap (m+1)) (P.η i) (Q.η j) Z rfl (by rw [hj]; exact (hp j).trans (L.large j).need) (bound_climb G a m) (hu ▸ hi j) (hT ▸ hi i) hΦ (H _ |>.2.2) (Q.price _) he
  obtain ⟨hy',hr,-⟩ := H m
  have hSat : Y.Bounds T'.clip T'.width T'.paths (a.clock.loopCap m) := hP _ _ _ (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (by rw [hj]; exact hy') hr
  refine ⟨Y,α,ρ, ⟨hE.trans (show d j ≤ U.drift from hu ▸ hq _), ⟨hX,hY,hSat⟩,fun t v => ⟨hK t v,(hρ t v).1, (hρ t v).2.1,?_,?_⟩⟩⟩
  · exact Bid.one_for_all (a.clock.op m t) Work.F05.answer (hg t) (fF t) U.clip T'.clip R Y U.width U.paths _ _ (Q.price _) hy Z he (ρ t) (fun F=> (hρ t F).1) (hK t) (hG t) v
  have hn : W.shells j ≤ (f t).val := (Nat.le_mul_of_pos_right _ (by positivity)).trans (h.volume m t)
  have hr := transfer_bound (hg t) hy he (Q.price j) (hρ t v).1 (hρ t (fF t)).1 (hK t v) (hK t _) (H' (F j M.L) (g j) le_rfl le_rfl t)
  apply higher_bill hr
  simp only [mul_one]; rw [hj]; exact ht _ _ hn
end level
end YM.Stationary
end

/-!
# Decrement to zero planting F orientations on the stamped beds. Use
 Horizon-retained rows; Kernel must not silently replace p/sector camera.
 `path` extends by junk only above N (all actual p on `side`). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}

structure FullPaths (K : Kin V Z) (Q : PostCost L) : Prop where
  linked : K.Planned Q
  row N m : m ≤ N → (K.path N m).row=rowPath (V.H N m)
  allPeriods N m i (F : Forest (a.clock.op m i).ratio) : m<N → FiniteBound F (K.path N (m+1)) (K.path N m) (a.params (m+1)).clip (a.params m).clip (K.alpha N m) Z
      (K.stationary N m i F) (Q.Γ (a.clock.J (m+1))) (Q.c (a.clock.J (m+1))) 1

lemma plowed (h : Paid w a) (hl : ∀ i, 1 ≤ a.clock.loopCap i) (hp : ∀ N,∃ R : PathData G,BranchRow V N R)
    (hr : ∀ m N,m<N →∀ R, SatPath V N (m+1) R → ∃ D α ρ,Bubble V Q Z N m R D α ρ) : ∃ T : Kin V Z, FullPaths T Q := by
  classical
  have he (N n) (hN : n≤N) :
      ∃ Y : ℕ→PathData G,∃ α : ℕ→ℝ,∃ ρ : ∀ i,GainWire a i,BranchRow V N (Y N) ∧
        (∀ i,n ≤ i → i≤N → SatPath V N i (Y i)) ∧ ∀ i, n ≤ i → i < N → Bubble V Q Z N i (Y (i+1)) (Y i) (α i) (ρ i) := by
    induction hN using Nat.decreasingInduction with
    | self =>
      obtain ⟨R,H⟩ := hp N
      refine ⟨fun _=> R,0,fun _ _ _ _=>0,H,fun i hi hu=> ?_,by intros; omega⟩
      rw [le_antisymm hu hi]; exact H.1
    | of_succ i hi I =>
      obtain ⟨Y,α,ρ,hY,he,H⟩ := I
      obtain ⟨D,w,θ,hD⟩ := hr i N hi _ (he (i+1) le_rfl hi)
      refine ⟨update Y i D,update α i w,update ρ i θ,?_,?_,?_⟩
      · rw [update_of_ne hi.ne']; exact hY
      · intro m hm hv; rcases eq_or_lt_of_le hm with heq|heq
        · subst m; rw [update_self]; exact hD.lives
        rw [update_of_ne heq.ne']; exact he m (Nat.succ_le_of_lt heq) hv
      intro m hv hx; rcases eq_or_lt_of_le hv with heq|heq
      · subst m; rw [update_self,update_self,update_self,update_of_ne (by omega)]; exact hD
      rw [update_of_ne (by omega : m+1 ≠ i),update_of_ne (by omega : m≠i),update_of_ne (by omega : m ≠ i),update_of_ne (by omega : m≠i)]; exact H m heq hx
  choose Y α ρ H H' HI using fun N=> he N 0 (Nat.zero_le _)
  let V0 : Kin V Z := ⟨α,Y,ρ⟩; refine ⟨V0,?_,fun N m h=> (H' N m (by omega) h).row,fun N m p F hm=> (HI N m (by omega) hm|>.steps p F).2.2.2.2⟩
  refine ⟨h.stage.symm,h.lengths.symm,fun N m hm=> (H' N m (by omega) hm).ties,fun N m hm => (H' N m (by omega) hm).bound,
    fun N i=>(H N).2.1 i,fun N i=> (H N).2.2 i,fun N m p hm F=>(HI N m (by omega) hm|>.steps p F).1,
    fun N m p hm F=>?_,fun N m p hm F=> (HI N m (by omega) hm|>.steps p F).2.2.2.1,fun N m hm=> (HI N m (by omega) hm).earns,fun N m p hm F=> ?_⟩
  · exact ⟨(HI N m (by omega) hm|>.steps p F).2.1,(HI N m (by omega) hm|>.steps p F).2.2.1⟩
  exact higher_bill ((HI N m (by omega) hm|>.steps p F).2.2.2.2) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl _) (Q.pos _).le) (Real.exp_pos _).le)
end YM.Stationary
end

/-!
# Schedule payment & production. Charges before Rolls; shell threshold
chosen freely after to upgrade exponential to a common amplitude.

Suffices is neither needed nor promised by our proofs: Retained's
H, A and T from pinning ensure applicability to the **same** data.
Here WP HorizCalc is still a lemma input, to be implemented.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : MapPrices} {K : KernelChoices} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}

lemma waits_up (C k H : ℝ) (hk : 0 < k) (hH : 0<H) : ∃ x : ℕ, ∀ n : Side, x≤n.val → C*Real.exp (-k*n.val) ≤ H*Real.exp (-(k/2)*n.val) := by
  have hp : Tendsto (fun x : ℕ=> -(k/2)*(x:ℝ)) atTop atBot := by simpa using tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (show -(k/2)<0 by linarith)
  obtain ⟨u,Hu⟩ := eventually_atTop.1 ((show Tendsto (fun j=> C*Real.exp (-(k/2)*(j:ℕ))) atTop (𝓝 0) by simpa using (Real.tendsto_exp_atBot.comp hp).const_mul C).eventually (ge_mem_nhds hH))
  refine ⟨u,fun n hn=> ?_⟩
  conv => arg 1; rw [show -k*n.val= -(k/2)*n.val+(-(k/2)*n.val) by ring,Real.exp_add,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Hu n.val hn) (Real.exp_pos _).le

structure Buys (s : Sheet G) (τ A d : ℕ→ℝ) (μ : ℕ → ℕ) (B : ℕ → ℝ) : Prop where
  axis (j : ℕ) : (s.profile j).clip.direct ≤ B j
  fields (j : ℕ) : (s.profile j).width=τ j ∧ (s.profile j).paths=A j
  gradient j : d j ≤ (s.profile j).drift
  days j : μ j≤s.floorL j

lemma under_contract (G : Gauge) (hS : G.Simple) (B : MapPrices) (K : KernelChoices) (B₀ : ℕ→ℝ) (he : ∀ i, 0 ≤ B₀ i) (h : Fluent G) :
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → ∃ U : Kin W Y,FullPaths U Q := by
  obtain ⟨σ,A,hσ,hA,H,P⟩ := claiming G hS K B B₀ he
  refine ⟨σ,A,hσ,hA,fun τ A' ht hv hw => ?_⟩
  obtain ⟨d,y,u,F,W,h1,Lh⟩ := P τ A' hv (fun i => (hA _).trans (hw _)) h
  refine ⟨d,fun i=> y i/2,u,fun i=>(h1 i).1,fun i=> half_pos (h1 i).2,fun s hs hB L => ?_⟩
  obtain ⟨η,H'⟩ := scene_gate L B
  choose V hT using fun i => waits_up (F i (L.L i)) (y i) 1 (h1 i).2 zero_lt_one
  refine ⟨fun i=> max (GateVolume i) (V i),η,H',fun Θ=> ?_⟩
  obtain ⟨Δ,hΔ⟩ := clocks G hS s L Θ (fun i=> W i (L.L i))
  refine ⟨Δ,fun w β b he hl Q hη hg hc a hd X Y hx hy Z HZ => ?_⟩
  have hw₀ := hΔ w β b he a hd
  have hpW i : (s.profile i).width ≤ σ i := (hB.fields i).1.trans_le (ht i)
  have hk i : A i ≤ (s.profile i).paths := (hw i).trans_eq (hB.fields i).2.symm
  have hg' i (n : Side) (hL': w.shells i ≤ n.val) : F i (L.L i) * Real.exp (-(y i)*n.val) ≤ Q.Γ i*Real.exp (-(Q.c i)*n.val) := by
    have hh : Q.c i ≤ y i/2 := hc i
    have hξ : 1≤Q.Γ i := hg i
    refine (hT i n ((le_max_right ..).trans ((hl i).trans hL'))).trans (mul_le_mul hξ (Real.exp_monotone (by gcongr)) (Real.exp_pos _).le (zero_le_one.trans hξ))
  refine plowed hd (fun i=> (hw₀ i).2.2) (fun N=> budding hd hpW hk hB.axis hx hy H (fun i => (hw₀ _).2.2) N) fun m N hN R hR => ?_
  refine energized hd (hη.symm ▸ H') (fun i=> le_trans (le_max_left ..) (hl i)) hg' hB.axis hpW hk hB.gradient hB.days HZ hx hy ?_ hw₀ hR.bound hR.ties hN
  rw [hs]; rw [funext fun i=> (hB.fields i).1,funext fun i=> (hB.fields i).2]; exact Lh
end YM.Stationary
end
