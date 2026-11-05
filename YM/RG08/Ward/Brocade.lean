import YM.RG08.Ward.Perch
/-! # Faithful analytic germs witness (ONE finite step; still winding) -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} {G : Gauge} {F : Verse (Loc G 1)} {n : ℕ}
def SoftArc (m : Side)(k : ℕ)(p : Air G) (Q : Pot G 2) (q : ℕ) : Prop := ∀ V W : ℝ→Link G m,
    AnalyticAt ℝ V 0→ V 0=0→ AnalyticAt ℝ W 0 → W 0=0→ EquivalentNear V W→ Fit (k+1) (grand k (sector Q p q) m ∘ V) (grand k (sector Q p q) m ∘ W)
lemma Tune_sector (p : Air G) (Q : Pot G 2) (he : ∀ i j,Tunable (p i j)) (hp : Tunable Q) (j k) : Tunable (sector Q p j k) := by
  unfold sector; split; exact Tunable.zero ..; apply he; next n=>
    split; next h=> rw [show n=0 by omega]; rw [prolong_self]; exact hp -- `n` indexes?
    exact he ..
lemma opus_whole (F : Verse (Loc G 1)) (n) (m) : Grass (grand n F m) := Grass.list (fun i _=> Grass.base (Hemi.pos (recital (F i) m)))
lemma prospect (F : Verse (Loc G 1)) (n) (m) (x : Link G m) : (fun t:ℝ=>grand n F m (t • x))=peval (fun i=> stanza (F i) m x) n := by
  funext t; unfold grand peval PertExtension.Series.Zone.eval; rw [Finset.sum_apply]; exact sum_congr rfl fun i _=> mnemonic ..
lemma opus_jet (F : Verse (Loc G 1)) (hp : ∀ j,Tunable (F j)) (n m) (j)(hj : j≤n) : Tensor.coeff (grand n F m) j 0= recital (F j) m := by
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm ((opus_whole F n m).smooth.contDiffAt|>.of_le le_top)) ((hp j).2.2 m)
  funext x; rw [← jet_coefficient,← pulse_ray _ _ ((opus_whole F n m).smooth.contDiffAt.of_le le_top)]
  rw [prospect]; exact congr_fun ((ink_aspire ((peval_stop n _).contDiffAt.of_le le_top)).unique (Aspiration.polynomial _ _)) j |>.trans (if_pos hj)

section converse
variable (n : ℕ)(p : Air G)(Q : Pot G 2)(q : ℕ)(m : Side) -- infer via h
private lemma honorQ (h : SoftArc m n p Q q) (x : Link G m)(s : G.El) : grand n (sector Q p q) m (stain s x)= grand n (sector Q p q) m x := by
  let R:= grand n (sector Q p q) m; let X (t:ℝ):= t • x; let y:= stain s x; let Y (t:ℝ):= t • y; let U:=sector Q p q
  have he: EquivalentNear X Y := Or.inr ⟨(fun _ _=> s),s,tendsto_const_nhds,Eventually.of_forall (fun t=> by unfold Y y X;rw [← map_smul,stain_cons])⟩
  have hv := h X Y (contDiffAt_id.smul contDiffAt_const|>.analyticAt) (zero_smul ..) (contDiffAt_id.smul contDiffAt_const|>.analyticAt) (zero_smul ..) he
  have Hp z (i) (hi : i≤n) : ink (fun t:ℝ=>R (t•z)) i=stanza (U i) m z := by
    rw [show (fun t:ℝ=>R (t•z))=_ from prospect U n m z];
    exact congr_fun ((ink_aspire ((peval_stop n _).contDiffAt.of_le le_top)).unique (Aspiration.polynomial _ _)) i |>.trans (if_pos hi)
  have Hz z : Aspiration (fun t:ℝ=>R (t•z)) (ink (fun t:ℝ=>R (t•z))) :=
    ink_aspire ((opus_whole U n m).smooth.contDiffAt.of_le le_top|>.comp _ (contDiffAt_id.smul (contDiffAt_const (c:=z))))
  have Ht i (hi:i≤n): stanza (U i) m x = stanza (U i) m y := by rw [← Hp _ _ hi,← Hp _ _ hi]; exact aspiredV hv (Hz _) (Hz _) hi
  unfold grand; rw [Finset.sum_apply, Finset.sum_apply]; exact sum_congr rfl fun i hi=> Eq.symm (Ht i (Nat.le_of_lt_succ (mem_range.mp hi)))
private lemma footprint (h : SoftArc m n p Q q) (s : Signed) (x : Link G m) :
    let Z := grand n (sector Q p q) m; let X := fun t:ℝ=>t • x
    Fit (n+1) (fun t:ℝ=> statue Z s (input G m (t•x))) (Z∘X) := by
  intro Z X
  let A := orderTurn s (G:=G) (m:=m); let Y (t:ℝ):= A (X t)
  have hr t : input G m (Y t)= pull s 0 (input G m (X t)) := Eq.symm (flip_links ..)
  let R t := foyer (input G m (Y t)); let V (t:ℝ):= content (R t)
  have hx:ContDiffAt ℝ ω X 0:=contDiffAt_id.smul contDiffAt_const; have hY: ContDiffAt ℝ ω Y 0:= A.contDiff.contDiffAt.comp _ hx
  have hu:X 0=0:= zero_smul ..; have hn:Y 0=0:=by unfold Y; rw [hu,map_zero]
  have ht:R 0=1:=by unfold R; rw [hn]; simp
  have hG:Army (input G m∘Y) 0 := Army.powL hY
  have hR:Army R 0 := foyer_hol hG; have Hv := hR.logL ht
  have hv:V 0=0:=by unfold V; rw [ht,content_one]
  have H:EquivalentNear Y V := by
    let d:= fun t=> embassy (input G m (Y t))
    have Hd : Tendsto d (𝓝 0) (𝓝 (1 : Coats G m)) := by
      have he:ContinuousAt d 0 := embassy_c.continuousAt.comp hG.cont
      have hh: d 0=1:= by unfold d; rw [hn]; simp [outset]
      exact hh ▸ he.tendsto
    exact Or.inr ⟨d,1,Hd,(ht ▸ hR.cont.tendsto).eventually content_encodes⟩
  rw [show (fun t:ℝ=> statue Z s (input G m (t•x)))= Z∘V from funext fun t=> by unfold statue; rw [← show _=_ from hr t]; rfl]
  exact Fit.turn ((h X Y hx.analyticAt hu hY.analyticAt hn (Or.inl ⟨s,Eventually.of_forall hr⟩)).join (h Y V hY.analyticAt hn Hv.analyticAt hv H))
-- grade=loop length itself. Produce witness WITH ALL jets; no gauge equations assumed beyond isolated arcs
lemma opines (h : SoftArc m n p Q q) (he : ∀ i j,Tunable (p i j)) (hp : Tunable Q) : ∃ f:Link G m→ℝ,Pointwise f∧ ∀ j≤n, Tensor.coeff f j 0= recital (sector Q p q j) m := by
  let Z:=sector Q p q; let R:=grand n Z m; let g:=resplendent R ∘ input G m
  have hb : Pointwise g := shining R (fun u x=> honorQ n p Q q m h x u) (opus_whole Z n m).smooth.contDiffAt
  refine ⟨g,hb,fun i hi=>?_⟩; rw [← opus_jet Z (Tune_sector p Q he hp q) n m i hi]
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm (hb.analytic.contDiffAt.of_le le_top)) (Tensor.coeff_symm ((opus_whole Z n m).smooth.contDiffAt.of_le le_top)); funext x
  -- Fit after exact average (finite).
  let V (t:ℝ):= g (t•x); let U (t:ℝ):= R (t•x); have hc : Fit (n+1) V U := by
    let N := (Fintype.card Signed:ℝ); have hz:0<N:= by unfold N; positivity
    have ht := Fit.emp (s:=univ) (fun i (_: i ∈ (univ:Finset Signed))=> footprint n p Q q m h i x) |>.scale N⁻¹
    change Fit (n+1) V (N⁻¹ • fun t:ℝ=> ∑ _ : Signed,U t) at ht
    rw [show (N⁻¹ • fun t:ℝ=>∑ _ : Signed, U t)= U from funext fun t=> by erw [Pi.smul_apply,sum_const,card_univ,smul_eq_mul,nsmul_eq_mul]; rw [inv_mul_cancel_left₀ hz.ne']] at ht -- defeq?
    exact ht
  exact aspiredV hc (directions (hb.analytic.contDiffAt.of_le le_top) x) (directions ((opus_whole Z n m).smooth.contDiffAt.of_le le_top) x) hi
end converse
lemma opines_true {p : Air G}{Q : Pot G 2} (h : Beacon m p Q) (H : Decked p)(hc:Halt p)(hz:∀ i j,Tunable (p i j)) (hp : Tunable Q) : Faithful Q p m := by
  intro q n; obtain ⟨F,Hf,hh⟩:=opines (n+2) p Q q m (fun _ _ hx hv hy he hre=> parts_arc h H hc hx hv hy he hre n q) hz hp; exact ⟨F,Hf,fun j hj=> hh j (by omega)⟩
end YM.RG08.Reflect
