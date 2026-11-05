import YM.FullVolume.Region

/-!
# Full real Gate. Only need point Cauchy from physical dynamics at generic
(non-tie) probes. Recovery here for all compacts in torus separation. No
diagonal in this lemma, nor any additional mesh selection in PointPurchased.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G} (M : FixedBounds C)(e : Extraction.Sequence) {v : Fin 0 → C.book.Token}
variable {n:ℕ}(p : ℕ)(v : Fin n → C.book.Token)(l:List (MotionIndex n))

def evaluate (C:Family G)(e:Extraction.Sequence)(p:ℕ)(v: Fin n→C.book.Token)(l:List (MotionIndex n))
    (i:ℕ)(x:Points n):= gKernel C v l (e i) p (address (C.S.a (e i)) x)

def Tuned (C:Family G)(e:Extraction.Sequence)(p:ℕ)(v: Fin n→C.book.Token)(l:List (MotionIndex n)) (g:Points n→ℂ) := Meets (NoHit C.S p n) (evaluate C e p v l) g

lemma returns {f:Points n→ℂ}(h:Tuned C e p v l f) {x:Points n} (hx:x∈NoHit C.S p n) {q : ℕ → Positions n} (he:Tendsto (fun i=> tag (C.S.a (e i)) (q i)) atTop (𝓝 x)) :
    Tendsto (fun i=> gKernel C v l (e i) p (q i)) atTop (𝓝 (f x)):=by
  obtain ⟨K,hK,hT,hV⟩:=exists_compact_subset (nohitOpen C.S p n) hx
  let u i:= tag (C.S.a (e i)) (q i)
  have hv: Tendsto (fun i=> f (u i)) atTop (𝓝 (f x)):=
    ((h.continuousOn.continuousAt ((nohitOpen C.S p n).mem_nhds hx)).tendsto.comp he)
  refine hv.congr_dist (Metric.tendsto_nhds.mpr ?_)
  intro ε hε
  filter_upwards [h.uniform K hV hK ε hε, he.eventually (mem_interior_iff_mem_nhds.mp hT)] with i hi hp
  rw [dist_zero_right, Real.norm_of_nonneg (by positivity), dist_comm]
  have he:=hi (u i) hp; unfold evaluate u at he; rwa [address_matched (C.S.a_pos ..)] at he

lemma nearest {v:ℝ}(hv:0<v): ∀ᶠ i in atTop, ∀ x:Points n, dist (tag (C.S.a (e i)) (address (C.S.a (e i)) x)) x< v:=by
  have hl: Tendsto (fun i=> (4*n:ℝ)*C.S.a (e i)) atTop (𝓝 0):= by simpa using! ((C.S.shrinks.comp e.cofinal).const_mul (4*n:ℝ))
  filter_upwards [hl.eventually (gt_mem_nhds hv)] with i hi x using (approximate (C.S.a_pos _) x).trans_lt hi

include M
lemma circulating : oscillation (NoHit C.S p n) (evaluate C e p v l):= by
  intro K hU hK ε hε
  obtain ⟨t,ht,hT⟩:= hK.exists_cthickening_subset_open (nohitOpen ..) hU
  obtain ⟨r,B,hr,hB,H⟩:= M.localLip v l p hT hK.cthickening
  let g:= min r (ε/(B+1))
  have hg: 0<g := lt_min hr (by positivity)
  have hv: 0<g/4:= by positivity
  refine ⟨g/4,hv,?_⟩
  filter_upwards [e.cofinal.eventually H,nearest (n:=n) (C:=C) e ht, nearest (n:=n) (C:=C) e hv] with i hi he hF x hx y hy hw
  let a:= C.S.a (e i); let f x := tag a (address a (x: Points n))
  have hl : f y∈ cthickening t K:= mem_cthickening_of_dist_le _ _ _ _ hy (he y).le
  have hz : dist (f x) (f y) < g := by
    have hv' := hF y; change dist (f y) y<g/4 at hv'; rw [dist_comm] at hv'
    have ht:=hF x; change dist (f x) x<_ at ht; linarith [dist_triangle (f x) x y, dist_triangle (f x) y (f y)]
  apply lt_of_le_of_lt (hi _ _ hl (hz.le.trans (min_le_left ..))); change B*dist (f x) _ < _
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz.le hB); have hw:= (le_div_iff₀' (by positivity : 0 < B+1)).1 (min_le_right r (ε/(B+1)))
  change (B+1)*g ≤ ε at hw; linarith

omit M in
/-- Main gate. Point data may use ordinary Representatives. -/
def Purchased (C:Family G)(e: Extraction.Sequence) : Prop:= ∀ (n p:ℕ) (v: Fin n→ C.book.Token) x, x∈Cyclic C.S p n → CauchySeq (fun i=> evaluate C e p v [] i x)

lemma established (hp:Purchased C e):∃ f,Tuned C e p v [] f:= by
  exact growFrom (nohitOpen ..) (circulating M e p v []) (Cyclic C.S p n) (MeasureTheory.Measure.dense_of_ae (almostCyclic C.S p n)) (fun x hx=>hp _ _ _ x hx.1)

omit M in
lemma forwardPrice {t : ℝ}(ht:0<t):Tendsto (fun N=> (steps C.S t N:ℝ)*C.S.a N) atTop (𝓝 t):=by
   have he:= tendsto_const_nhds (f:=atTop) (x:=t) |>.add (C.S.shrinks)
   rw [add_zero] at he; refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ :ℕ=> t) tendsto_const_nhds he ((step_upper C.S ht).mono ?_) (Eventually.of_forall (fun i=>?_))
   · intro i hi; exact hi.2.1
   have hp:= C.S.a_pos i
   exact (mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg ht.le hp.le)).le hp.le).trans_eq (by rw [add_mul,one_mul,div_mul_cancel₀ _ hp.ne'])

set_option maxHeartbeats 600000 in
lemma from_previous {f : Points n→ℂ}(h:Tuned C e p v l f) (a:MotionIndex n) : ∃ g,Tuned C e p v (a::l) g:=by
  apply growFrom (nohitOpen ..) (circulating M e p v (a::l)) univ dense_univ
  rintro x ⟨-,hx⟩
  obtain ⟨K,hK,hT,hU⟩:= exists_compact_subset (nohitOpen ..) hx
  obtain ⟨B,r,hB,hr,H⟩:= M.taylor v l p hU hK
  obtain ⟨t,ht,hS⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hT)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let q:= min (t/2) (min (r/3) (ε/(8*(B+1))))
  have hp:0<q:= lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have ht': 2*q ≤ t:= by have h' : q≤t/2 := min_le_left ..; linarith
  obtain ⟨hr',hb'⟩ : q ≤ r/3 ∧ q ≤ ε/(8*(B+1)):= le_min_iff.mp (min_le_right ..)
  let T N:= e N; let Y i:= address (C.S.a (T i)) x
  let b N:= steps C.S q N; let s i:=C.S.a (T i)
  let k i:ℝ:= b (T i)*s i; let z i:=Y i + b (T i) • drive a; let w:=x+q • Dir a
  let F i:= gKernel C v l (T i) p
  let D i:=evaluate C e p v (a::l) i x
  have hg:Tendsto k atTop (𝓝 q) := (forwardPrice hp (C:=C)|>.comp e.cofinal)
  have hh:Tendsto (fun i=> tag (s i) (Y i)) atTop (𝓝 x):=(Extraction.chosen x).comp e.cofinal
  have hy:Tendsto (fun i=> tag (s i) (z i)) atTop (𝓝 w):= by
    simp_rw [z,taggedN]; exact hh.add (hg.smul_const _)
  have he i: dist (tag (s i) (z i)) (tag (s i) (Y i))=k i:=paidDist _ _ (C.S.a_pos _) _ _
  have hw : w∈ NoHit C.S p n:= by
    refine hU (hS (mem_closedBall.mpr ?_))
    apply le_of_tendsto (hy.dist hh)
    filter_upwards [e.cofinal.eventually (step_upper C.S hp)] with i hi
    rw [he]; exact hi.2.2.trans ht'
  have hW:Tendsto (fun i=> F i (z i)) atTop (𝓝 (f w)):= returns e p v l h hw hy
  have hY:Tendsto (fun i=> F i (Y i)) atTop (𝓝 (f x)):= returns e p v l h hx hh
  let W (i : ℕ):= (k i)⁻¹ • (F i (z i)- F i (Y i))
  have hP := Metric.cauchySeq_iff.mp (((hg.inv₀ hp.ne').smul (hW.sub hY)).cauchySeq) (ε/2) (half_pos hε)
  obtain ⟨L,hL⟩:=hP
  have heq : ∀ᶠ i in atTop, dist (W i) (D i) ≤ ε/4:=by
    filter_upwards [hh.eventually (mem_interior_iff_mem_nhds.mp hT),e.cofinal.eventually (step_upper C.S hp), e.cofinal.eventually H] with i hi h hp'
    have hk: q ≤ k i ∧ k i ≤ 2*q := h.2
    have h0:0<k i:=hp.trans_le hk.1
    have hq: ‖F i (z i)- F i (Y i)- k i • D i‖≤ B*(k i)^2:=by
      have hv:= hp' (Y i) (z i) hi (show dist (tag (s i) (z i)) (tag (s i) (Y i)) ≤ r from (he i).trans_le (by linarith only [hk.2,hr',hr]))
      dsimp only at hv
      rw [show dist _ _ = k i from he i, taggedN,add_sub_cancel_left,map_smul,loyal] at hv -- anchor z unfolding
      exact hv
    rw [dist_eq_norm,show W i-D i= (k i)⁻¹ • (F i (z i)-F i (Y i)-k i • D i) by rw [smul_sub,inv_smul_smul₀ h0.ne'],
      norm_smul,Real.norm_of_nonneg (inv_pos.mpr h0).le]
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (inv_pos.mpr h0).le
      _ = B*k i:=by field_simp
      _ ≤ ε/4:=by
        have hev:= (le_div_iff₀' (by positivity : 0<8*(B+1))).1 hb'; nlinarith only [hev, hp,hk.2,hB,mul_le_mul_of_nonneg_left hk.2 hB]
  obtain ⟨j,hj⟩:= eventually_atTop.mp ((eventually_ge_atTop L).and heq)
  refine ⟨j,fun m hm n hn=>?_⟩
  change dist (D m) (D n)< _
  obtain ⟨he,hM⟩:=hj m hm; obtain ⟨hf,hN⟩:=hj n hn
  have h:= hL m he n hf; change dist (W m) (W n)< _ at h; rw [dist_comm] at hM
  linarith [dist_triangle (D m) (W m) (W n),dist_triangle (D m) (W n) (D n)]
end YM.FullVolume
