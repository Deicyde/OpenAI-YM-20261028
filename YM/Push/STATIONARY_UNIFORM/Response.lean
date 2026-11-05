import YM.Push.STATIONARY_UNIFORM.ImplicitRadius
import YM.Push.STATIONARY_UNIFORM.Touch

/-!
# Locality of stationary branch and stationary actions, from connection estimates

Derive on-shell real bounds on the SAME continued solution. Strength/cost are
those of the real tensor-localization estimates; potentially usable before
proving strip estimates of smaller coefficient bounds on smooth routed input
classes. Does not attempt those sharper estimates. Response can test general
inhomogeneous inputs, does not require repeating tree choices. No assumed
analytic continuation width for the tree or paths. The radius and rate
parameters remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical

variable {ι τ : Type} [Fintype ι] [Fintype τ]
variable {n : Side} {N k K : ℕ} {x : Positions ι} {l : ι⊕τ → Site n}
    {a r C m R : ℝ} {f : Positions (ι ⊕ τ) → ℝ} {g : Positions ι → Positions τ}

def Envelope (l : ι → Site n) (m : τ → Site n) (a : ℝ) (k : ℕ) (f : Positions ι → Positions τ) (x : Positions ι) (C : ℝ) :=
  ∀ (i : ℕ), i≠0 → i≤k → ∀ q : Fin i → ι, ∀ j, ‖entry f x q j‖ ≤ C*glaze l (m j) q a

lemma Envelope.more_cost {l : ι → Site n} {m : τ → Site n} (h : Envelope l m a k g x C) (hp : C ≤ R) : Envelope l m a k g x R :=
  fun i hn hi q j => (h i hn hi q j).trans (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)

lemma boltJet (q : Fin (k+1) → ι) (x : Positions ι) : entry id x q = if k=0 then bolt (q 0) else 0 := by
  unfold entry
  by_cases hk : k=0
  · subst k; simp
  simp only [if_neg hk]; rw [iteratedFDeriv_succ_apply_right]
  simp only [fderiv_id]
  rw [iteratedFDeriv_const_of_ne hk]; rfl

def upperCol : Positions ι →L[ℝ] Positions (ι ⊕ τ) :=
  (partSpace ι τ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Positions ι) (Positions τ))
lemma upper_bolt (i : ι) : upperCol (τ:=τ) (bolt i) = bolt (Sum.inl i) := by
  funext j; cases j with
  | inl j => change bolt i j = bolt (Sum.inl i) (Sum.inl j); by_cases he : j=i <;> simp [bolt,he]
  | inr j => change 0=bolt (Sum.inl i) (Sum.inr j); simp [bolt]

def curve (g : Positions ι → Positions τ) (x : Positions ι) := meetVar x (g x)

lemma along (hg : ContDiffAt ℝ ω g x) : ContDiffAt ℝ ω (curve g) x :=
  (partSpace ι τ).symm.contDiff.contDiffAt.comp (f:=fun k => (k,g k)) x (contDiffAt_id.prodMk hg)

lemma curve_step (hg : ContDiffAt ℝ ω g x) (q : Fin (k+1) → ι) :
    entry (curve g) x q = upperCol (entry id x q)+lowerCol (entry g x q) := by
  let T := (partSpace ι τ).symm
  let B i := (i, g i)
  have hB : ContDiffAt ℝ ω B x := contDiffAt_id.prodMk hg
  have hh : entry (curve g) x q=T (entry B x q) := by unfold entry; rw [show curve g=T.toContinuousLinearMap ∘ B from rfl,T.toContinuousLinearMap.iteratedFDeriv_comp_left hB le_top]; rfl
  rw [hh, show entry B x q = (entry id x q, entry g x q) from ?_]; exact meet_columns ..
  unfold entry
  rw [show iteratedFDeriv ℝ (k+1) B x=_ from iteratedFDeriv_prodMk (contDiffAt_id (n:=ω)) hg (i:=k+1) le_top]; rfl

lemma higher_positions (hg : ContDiffAt ℝ ω g x) (j : τ) (q : Fin (k+1) → ι) : entry (curve g) x q (Sum.inr j) = entry g x q j := by rw [curve_step hg]; change (0:ℝ)+entry g x q j=_; rw [zero_add]

-- slope coordinate as horizontal or vertical derivative of f. -
def coordinate (f : Positions ι → ℝ) (u : ι) (p : Positions ι) := fderiv ℝ f p (bolt u)
lemma coord_eq (f : Positions ι → ℝ) (u : ι) : coordinate f u=fun p => entry f p ![u] := by funext p; unfold coordinate entry; simp

lemma varied (hf : ContDiffAt ℝ ω f (curve g x)) (i : τ) (j : ι⊕τ) :
    fderiv ℝ (coordinate f (Sum.inr i)) (curve g x) (bolt j)=entry f (curve g x) ![j,Sum.inr i] := by
  rw [coord_eq]; exact (tend_entry hf _).2 _

/-- Common rate can pay repeated exchanges up to order N inclusive, no shrink
in the inductive hypothesis. Still a possibly much weaker rate than the
coarse-strip tests on generated precision data. -/
def responseRate (K N : ℕ) (C a M : ℝ) := min (weaker N a) (weaker N (tiltWidth K (M/2) a C))

def feedback (K : ℕ) (C a P : ℝ) (k : ℕ) := C+(Fintype.card (OrderedFinpartition (k+1)):ℝ) * (C*(1+P*(K*countCost (a/2)))^(k+1))

def curveCost (K : ℕ) (C a M : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 =>
    let d := tiltWidth K (M/2) a C
    curveCost K C a M j + feedback K C a (curveCost K C a M j) j * (M/2/2)⁻¹ * ((K:ℝ) * countCost (d/2))

section Loop
-- input hypotheses ONLY at point x on graph of function stationary on its nhd. Allows along unique path e.g. not launching a new gauge branch.
variable (h : Receipt l a N K C r m f)
include h
lemma rate_pos : 0<responseRate K N C a m := by
  have hM := h.pos_a; have hh : 0 < tiltWidth K (m/2) a C := tiltWidth_pos K (half_pos h.pos_m) hM h.pos_C.le
  unfold responseRate weaker; positivity
lemma curveCost_ge (k : ℕ) : 1 ≤ curveCost K C a m k := by
  have he := h.pos_C; have hm := h.pos_m; have ha := h.pos_a
  have hp := count_pos (half_pos ha); have hq := count_pos (half_pos (tiltWidth_pos K (half_pos hm) ha he.le))
  induction k with
  | zero => exact le_rfl
  | succ k ih => unfold curveCost feedback; refine ih.trans (le_add_of_nonneg_right ?_); positivity

lemma inverse_feedback (hg : ContDiffAt ℝ ω g x) (hz : curve g x∈closedBall 0 (reserveH K C a r m))
    (he : Slope f ∘ curve g =ᶠ[𝓝 x] 0) (hk : k+1 < N) (q : Fin (k+1) → ι)
    (H : Envelope (l ∘ Sum.inl) l (responseRate K N C a m) k (curve g) x (curveCost K C a m k)) :
    let P := entry g x q
    let z := l ∘ Sum.inl
    let G := block f (curve g x) *ᵥ P
    ∀ i, ‖G i‖ ≤ feedback K C a (curveCost K C a m k) k * glaze z (l (Sum.inr i)) q (responseRate K N C a m) := by
  intro P z Q i
  let A := l (Sum.inr i)
  let d := responseRate K N C a m; have hd : 0<d := rate_pos h
  let b := curveCost K C a m k; have hc : 1 ≤ b := curveCost_ge h _
  let Z := curve g
  let F := coordinate f (Sum.inr i)
  obtain ⟨ht,hp⟩ := h.born _ (closedBall_subset_ball h.reserveH_lt hz); change ContDiffAt ℝ ω f (Z x) at ht
  have hF : ContDiffAt ℝ ω F (Z x) := (ht.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
  let S := Finset.univ.erase (onePart k)
  let T (c : OrderedFinpartition (k+1)) := (ftaylorSeries ℝ F (Z x)).compAlongOrderedFinpartition (ftaylorSeries ℝ Z x) c
  let v : Fin (k+1) → Positions ι := fun i => bolt (q i)
  have hy : entry (F ∘ Z) x q=0 := by
    have hb : F ∘ Z =ᶠ[𝓝 x] 0 := by
      filter_upwards [he] with y hy; unfold F; rw [coord_eq]; exact congr_fun hy i
    unfold entry; rw [(hb.iteratedFDeriv ℝ _).eq_of_nhds, iteratedFDeriv_zero]; rfl
  let L := fderiv ℝ F (Z x)
  let Y := L (upperCol (entry id x q))
  have hh : (Y+Q i)+(∑ j∈S,T j) v=0 := by
    unfold entry at hy
    rw [comp_step (along hg) hF k] at hy
    change L (entry Z x q) + (∑ j∈S,T j) v=0 at hy
    rw [curve_step hg, map_add] at hy
    rw [show Q i = L (lowerCol P) from ?_]; exact hy
    change _ = (L ∘L lowerCol) P
    rw [by_row]
    apply Finset.sum_congr rfl
    intro j _
    change _ = P j * L (lowerCol (bolt j)); rw [lower_bolt, show L _ = _ from varied ht i (Sum.inr j)]
    exact mul_comm ..
  have hC := h.pos_C
  have hw := scatter_derivative f ht hp (Sum.inr i) hk
  let I := glaze z A q d
  have hI : 0 < I := Real.exp_pos _
  have hu : ‖Y‖ ≤ C * I := by
    unfold Y; by_cases hv : k=0
    · subst k; rw [boltJet,if_pos rfl,upper_bolt]
      rw [show L (bolt _) = _ from varied ht i _]; apply (hp _ hk ![Sum.inl (q 0),Sum.inr i] 1).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      unfold I glaze A z
      apply Real.exp_monotone
      simp only [spanSites, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change -a * ↑(separation A (l (Sum.inl (q 0)))+separation A A) ≤ -d* ((separation A (l (Sum.inl (q 0))):ℕ):ℝ)
      rw [separation_self,add_zero]; apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply neg_le_neg; apply le_trans (show d ≤ weaker N a from min_le_left ..); unfold weaker; have h := h.pos_a
      have ht : 0 ≤ (N:ℝ) := by positivity
      exact div_le_self h.le (by linarith)
    rw [boltJet,if_neg hv,map_zero,map_zero,norm_zero]; positivity
  let D : ℝ := C * (1+b*(K*countCost (a/2)))^(k+1); let W : ℝ := Fintype.card (OrderedFinpartition (k+1))
  have hM := count_pos (half_pos h.pos_a); have hP : 0≤b := le_trans zero_le_one hc
  have hG j (hj : j∈ S) : ‖T j v‖ ≤ D*I := by
    apply le_trans (wire_cost (p:=x) q j hk.le h.pos_a hd hC.le hP _ h.mult hw (f:=Z)
      (fun i p => H _ (j.partSize_pos i).ne' (smaller_parts j (Finset.ne_of_mem_erase hj) _) _ p))
    rw [min_eq_left (show d ≤ _ from min_le_left ..)]
    apply mul_le_mul_of_nonneg_right _ hI.le; apply mul_le_mul_of_nonneg_left _ hC.le
    have hD : 0 ≤ b*((K:ℝ)*countCost (a/2)) := by positivity
    apply le_trans (pow_le_pow_left₀ hD (le_add_of_nonneg_left zero_le_one) _)
    exact pow_le_pow_right₀ (le_add_of_nonneg_right hD) j.length_le
  have hl : ‖(∑ j∈S,T j) v‖ ≤ W * (D*I) := by
    rw [_root_.sum_apply]
    apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum hG))
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right (by unfold W; exact_mod_cast Finset.card_le_univ _) (by unfold D; positivity)
  change ‖Q i‖ ≤ (C+W*D)*I
  rw [show Q i = -(Y+(∑ j∈S,T j) v) from by linarith,norm_neg]
  apply ((norm_add_le ..).trans (add_le_add hu hl)).trans_eq; ring

lemma envelopes (hg : ContDiffAt ℝ ω g x) (hz : curve g x∈closedBall 0 (reserveH K C a r m))
    (he : Slope f ∘ curve g =ᶠ[𝓝 x] 0) {k : ℕ} (hk : k<N) :
    Envelope (l ∘ Sum.inl) l (responseRate K N C a m) k (curve g) x (curveCost K C a m k) := by
  induction k with
  | zero => intro i hi hi'; omega
  | succ k ih =>
    let Z := curve g
    let P := curveCost K C a m (k+1); have hP : 1 ≤ P := curveCost_ge h _
    have hh := ih (by omega)
    let c := responseRate K N C a m
    let d := tiltWidth K (m/2) a C
    let u := m/2/2
    let T := u⁻¹
    let W := feedback K C a (curveCost K C a m k) k
    have ht := curveCost_ge h k
    have hu : 0<d := tiltWidth_pos K (half_pos h.pos_m) h.pos_a h.pos_C.le
    have hT : 0<T := inv_pos.mpr (half_pos (half_pos h.pos_m))
    have hW : 0 ≤ W := by
      have hx := count_pos (half_pos h.pos_a); unfold W feedback; have := h.pos_C; positivity
    have hN : 0≤(K:ℝ)*countCost (d/2) := mul_nonneg (by positivity) (count_pos (half_pos hu)).le
    intro i hi hv
    rcases eq_or_lt_of_le hv with h'|h'
    swap
    · exact fun p j => hh.more_cost (show curveCost K C a m k ≤ P from le_add_of_nonneg_right
        (show 0≤ W*T*((K:ℝ)*countCost (d/2)) by positivity)) _ hi (by omega) p j
    subst i
    let M := block f (Z x); let β := l ∘ (@Sum.inr ι τ); let α := l ∘ (@Sum.inl ι τ)
    rintro p (i|i)
    · rw [curve_step hg]
      change ‖entry id x p i+0‖ ≤ P * _
      rw [boltJet,add_zero]; split
      next he =>
        subst k; by_cases hh : p 0=i
        · simpa [bolt,hh, glaze,spanSites,Fin.sum_univ_succ] using hP
        have hy : bolt (p 0) i=0 := by simp [bolt,Ne.symm hh]
        rw [hy,norm_zero]; exact mul_nonneg (le_trans zero_le_one hP) (Real.exp_pos _).le
      next he => simpa only [Pi.zero_apply,norm_zero] using mul_nonneg (le_trans zero_le_one hP) (show 0 ≤ glaze _ _ _ _ from (Real.exp_pos _).le)
    change ‖entry Z x p (Sum.inr i)‖ ≤ _; rw [higher_positions hg]
    let Q := entry g x p; let A := M *ᵥ Q
    have hf := inverse_feedback h hg hz he hk p hh
    obtain ⟨hD,H,_⟩ := h.priced_inverse (Z x) hz
    have hi : ‖Q i‖ = ‖∑ j, M⁻¹ i j * A j‖ := by
      change ‖Q i‖=‖(M⁻¹ *ᵥ A) i‖
      rw [show M⁻¹ *ᵥ A=Q by unfold A; rw [Matrix.mulVec_mulVec, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hD.ne'), one_mulVec]]
    have hs j : ‖M⁻¹ i j*A j‖ ≤ W*T*glaze α (β i) p c * Decay (d/2) (β i) (β j) := by
      rw [norm_mul]
      apply le_trans (mul_le_mul (show ‖M⁻¹ i j‖ ≤ T*Decay d (β i) (β j) from H i j) (hf j) (norm_nonneg _) (mul_nonneg hT.le (decay_pos ..).le))
      have hk := mul_le_mul_of_nonneg_left (path_price hk.le hu (rate_pos h) α (β i) (β j) p) (mul_nonneg hW hT.le)
      rw [min_eq_left (show c ≤ _ from min_le_right ..)] at hk
      change (T*Decay d (β i) (β j)) * (W*glaze α (β j) p c) ≤ _; unfold c
      linarith only [hk]
    change ‖Q i‖≤_; rw [hi]; apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun j _ => hs j)))
    rw [← Finset.mul_sum]
    apply le_trans (mul_le_mul_of_nonneg_left ((h.mult.comp Sum.inr_injective).count β (half_pos hu) (β i)) (mul_nonneg (by positivity) (Real.exp_pos _).le))
    change W*T*glaze α (β i) p c*_ ≤ (curveCost K C a m k+W*T*((K:ℝ)*countCost (d/2)))*glaze α (β i) p c
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (le_trans zero_le_one ht)) (Real.exp_pos _).le

-- cancellation lets us use derivatives through exactly n
omit h in
lemma main_horizontal (hg : ContDiffAt ℝ ω g x) (hf : ContDiffAt ℝ ω f (curve g x))
    (he : Slope f (curve g x)=0) (i : ι) :
    coordinate (f ∘ curve g) i x=coordinate f (Sum.inl i) (curve g x) := by
  let Z := curve g x; let L := fderiv ℝ f Z
  have ht (v : Positions τ) : L (lowerCol v)=0 := by
    change (L.comp lowerCol) v=0; rw [by_row]; apply Finset.sum_eq_zero; intro j _
    rw [show (L.comp lowerCol) (bolt j)=0 from ?_,smul_zero]
    change L (lowerCol (bolt j))=0; rw [lower_bolt]; have hz : Slope f Z j=0 := congr_fun he j
    simpa only [Slope,entry,iteratedFDeriv_one_apply,Matrix.cons_val_zero] using hz
  unfold coordinate
  rw [fderiv_comp _ (hf.differentiableAt (by simp)) ((along hg).differentiableAt (by simp))]
  have h1 : fderiv ℝ (curve g) x (bolt i)=upperCol (bolt i)+ lowerCol (entry g x ![i]) := by
    rw [show fderiv ℝ (curve g) x (bolt i)=entry (curve g) x ![i] by unfold entry; simp]
    rw [curve_step (k:=0) hg, boltJet]; simp
  change L (fderiv ℝ (curve g) x (bolt i)) = L _; rw [h1,map_add,ht,upper_bolt,add_zero]

def onShellCost (a C : ℝ) (K N : ℕ) (m : ℝ) :=
    (∑ i∈Finset.range N, (Fintype.card (OrderedFinpartition i):ℝ))*C *
        (1+curveCost K C a m (N-1)* ((K:ℝ)*countCost (a/2)))^N

lemma star_cost (hg : ContDiffAt ℝ ω g x) (hz : curve g x∈closedBall 0 (reserveH K C a r m))
    (he : Slope f ∘ curve g =ᶠ[𝓝 x] 0) :
    Scatter (l ∘ Sum.inl) (weaker N (responseRate K N C a m)) N (f ∘ curve g) x (onShellCost a C K N m) := by
  let Z := curve g; let p := Z x; let D := responseRate K N C a m
  let u := l ∘ (@Sum.inl ι τ); let U := curveCost K C a m (N-1)
  have hp : 0<N := lt_of_lt_of_le (by norm_num) h.order
  have hx' := envelopes h hg hz he (show N-1<N by omega)
  obtain ⟨hh,hS⟩ := h.born p (closedBall_subset_ball h.reserveH_lt hz)
  let B := 1+U*((K:ℝ)*countCost (a/2))
  have hd : 0<D:=rate_pos h; have hC := h.pos_C
  have hc : 0 ≤ U := le_trans zero_le_one (curveCost_ge h _)
  have hu : 0 ≤ U*((K:ℝ)*countCost (a/2)) := mul_nonneg hc (mul_nonneg (by positivity) (count_pos (half_pos h.pos_a)).le)
  have hB : 1 ≤ B := le_add_of_nonneg_right hu
  have hm := along hg
  have hv j : coordinate (f ∘ Z) j =ᶠ[𝓝 x] coordinate f (Sum.inl j) ∘ Z := by
    filter_upwards [he,hg.eventually (by simp), hm.continuousAt.tendsto.eventually (hh.eventually (by simp))] with y hy hj hk
    exact main_horizontal hj hk hy j
  intro k hk q i
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    let w : Fin k → ι := fun i => q i.castSucc
    let d := q (Fin.last k)
    have ha : entry (f ∘ Z) x q = entry (coordinate f (Sum.inl d) ∘ Z) x w := by
      have he := ((hv d).iteratedFDeriv ℝ k).eq_of_nhds
      unfold entry; rw [iteratedFDeriv_succ_apply_right,← he]; unfold coordinate -- peel last via iteratedFDeriv_comp_left
      let A := ContinuousLinearMap.apply ℝ ℝ (bolt d)
      rw [show (fun p => fderiv ℝ (f ∘ Z) p (bolt d)) = A ∘ fderiv ℝ (f ∘ Z) from rfl,
        A.iteratedFDeriv_comp_left ((hh.comp (f:=Z) x hm).fderiv_right (m:=ω) (by simp)) le_top]; rfl
    have ht : ContDiffAt ℝ ω (coordinate f (Sum.inl d)) p := by rw [coord_eq]; exact (tend_entry hh _).1
    let W := onShellCost a C K N m; have hW : 0 ≤ W := mul_nonneg (mul_nonneg (by positivity) hC.le) (pow_nonneg (show 0 ≤ B from zero_le_one.trans hB) _)
    let F := ftaylorSeries ℝ (coordinate f (Sum.inl d)) p; let T := ftaylorSeries ℝ Z x; let v (i) := bolt (w i)
    have he j : ‖(F.compAlongOrderedFinpartition T (j:OrderedFinpartition k)) v‖ ≤ C*B^N * glaze u (u d) w D := by
      apply le_trans (wire_cost w j (le_trans k.le_succ hk) h.pos_a hd hC.le hc (u d) h.mult
        (show Beacon l a k (coordinate f (Sum.inl d)) (u d) (Z x) C from scatter_derivative f hh hS _ hk)
        (f:=Z) (fun i p => hx' _ (j.partSize_pos i).ne'
          ((j.partSize_le i).trans (show k ≤ N-1 by omega)) _ p))
      rw [min_eq_left (show D≤_ from min_le_left ..)]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC.le) (Real.exp_pos _).le
      exact (pow_le_pow_left₀ hu (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ hB (le_trans j.length_le (by omega)))
    have hl : glaze u (u d) w D = glaze u (u d) q D := by
      unfold glaze spanSites; conv_rhs => rw [Fin.sum_univ_castSucc]; dsimp only [w,d]; rw [separation_self,add_zero] -- rhs etc
    change ‖entry (f ∘ Z) x q‖ ≤ W*glaze u (u (q i)) q _
    calc
      _ = ‖∑ j : OrderedFinpartition k, F.compAlongOrderedFinpartition T j v‖ := by rw [ha]; unfold entry; rw [iteratedFDeriv_comp ht hm le_top, FormalMultilinearSeries.taylorComp,_root_.sum_apply]
      _ ≤ W*glaze u (u d) w D := by
        apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun j _ => he j))); rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,← mul_assoc,← mul_assoc]
        have hi : (Fintype.card (OrderedFinpartition k):ℝ) ≤ ∑ i∈Finset.range N,(Fintype.card (OrderedFinpartition i):ℝ) := Finset.single_le_sum (f:=fun i => (Fintype.card (OrderedFinpartition i):ℝ)) (fun i _ => by positivity) (Finset.mem_range.mpr hk)
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hC.le) (pow_nonneg (zero_le_one.trans hB) _)) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [hl]; apply mul_le_mul_of_nonneg_left _ hW
        exact (price_relative hk q i hd.le).trans (mul_le_of_le_one_left (Real.exp_pos _).le (decay_le (half_pos hd).le _ _))
end Loop
end YM.Push.Uniform
