import YM.FullVolume.Panes

/-! Smearing and the connectedness-guarded kernel gates -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G} (e : Extraction.Sequence){S:Schedule}{p n:ℕ}

-- periodic cover convention even for differences
lemma periodic_delta {n : ℕ} (u:Positions n)(p:Reach n){F:Positions n→ℂ}(t:ℝ) (h:∀ x,F (x+u)=F x)(x): Reach.difference p t F (x+u)=Reach.difference p t F x:=by
  unfold Reach.difference; rw [add_right_comm x u (p.fore • _),h,show x+u-p.back • p.axis_=x-p.back • p.axis_+u by abel,h]
lemma periodic_variations (C : Family G) (p N n:ℕ)(v:Fin n→ C.book.Token)(q:Positions n)(h:wrap (C.side N p) ∘ q= (0:Fin n→Site (C.side N p)))(u:Positions n)(l:List (Reach n)) :
    squall (C.S.a N) l (lifted C N p v) (u+q)=squall (C.S.a N) l (lifted C N p v) u:=by
  induction l generalizing u with
  | nil=> unfold squall lifted; congr 1; funext i; change wrap (C.side N p) (u i + q i)=_; rw [map_add,show wrap (C.side N p) (q i)=0 from congr_fun h i,add_zero]; rfl
  | cons x l ih=> exact periodic_delta _ _ _ ih u

/-- For grid kernels in cover notation, use literal cell representatives
(right-closed) in joint test. Kernel should be periodic in this convention. -/
def sumOn (F:ℕ→Positions n→ℂ) (S:Schedule)(p N) (t:Test n):=
    (S.a N:ℂ)^(4*n)*∑ x:Var S n N p, t (tag (S.a N) (Lattice.lift ∘ x)) * F N (Lattice.lift ∘ x)
open Classical in
def stepping (F:ℕ→Positions n→ℂ)(S:Schedule)(p N)(t:Test n)(x:Points n) := (Fund S p n).indicator (fun x=> t (tag (S.a N) (address (S.a N) x))*F N (address (S.a N) x)) x

lemma stored (F:ℕ→Positions n→ℂ)(S:Schedule)(p N)(t:Test n) :
    Integrable (stepping F S p N t) ∧ (∫ x, stepping F S p N t x)=sumOn F S p N t:= by
  let g (x:Var S n N p):= t (tag (S.a N) (Lattice.lift ∘ x)) * F N (Lattice.lift ∘ x)
  have hp : stepping F S p N t=stair S g:=by
    funext x; unfold stepping stair
    by_cases h:x∈Fund S p n
    · rw [indicator_of_mem h,indicator_of_mem h]
      unfold g; rw [← show address (S.a N) x= Lattice.lift ∘ bucket N p (S:=S) x from (found (N:=N) h)]
    simp [h]
  rw [hp]; exact ⟨stair_int _,stair_integral g⟩

lemma usable {F:ℕ→Positions n→ℂ}{f:Points n→ℂ}(h:Cluster C e p n F f) (K:Set (Points n))(hK:IsCompact K)(hk:K ⊆ NoHit C.S p n) :∃ A:ℝ,0≤A∧ ∀ᶠ i in atTop, ∀ x:Positions n,tag (C.S.a (e i)) x∈ K → ‖F (e i) x‖ ≤ A:= by
  obtain ⟨A,hA⟩:= hK.bddAbove_image (h.1.norm.mono hk)
  let B:= max 0 A
  refine ⟨B+1,by unfold B; positivity,?_⟩
  by_contra! hv
  obtain ⟨s,hs,h⟩:= extraction_of_frequently_atTop hv; choose y hy hF using h
  obtain ⟨x,hx,w,hw,hW⟩:= hK.tendsto_subseq hy
  have hp:= ((show Cluster C e p n F f by assumption).2 x (hk hx) (fun i=> y (w i)) (s ∘ w) (hs.tendsto_atTop.comp hw.tendsto_atTop) hW)
  have ht: ‖f x‖ ≤ B:= (hA ⟨x,hx,rfl⟩).trans (le_max_right ..)
  obtain ⟨i,hi⟩:= (hp.norm.eventually (ge_mem_nhds (show ‖f x‖<B+1 by linarith))).exists; exact (hF (w i)).not_ge hi

lemma pudding {F:ℕ→Positions n→ℂ}{f:Points n→ℂ}(h:Cluster C e p n F f) (t:Test n)(ht:suitable C.S p t) : Integrable (fun x:Points n=> t x * f x) ∧
    Tendsto (fun j=> sumOn F C.S p (e j) t) atTop (𝓝 (t.applyTo f)):=by
  classical
  obtain ⟨D,hD,H⟩:= usable e h _ t.hasCompactSupport (readable C.S p t ht)
  obtain ⟨R,hR,hT⟩:= Order.testSup t
  let B:= (Fund C.S p n).indicator (fun _=>R*D)
  have hb : Integrable B:= (integrable_indicator_iff (full_box ..).1).mpr (integrableOn_const (full_box ..).2.ne)
  let g i:=stepping F C.S p (e i) t
  have hm i:AEStronglyMeasurable (g i) volume:= (stored F C.S p (e i) t).1.aestronglyMeasurable
  have hP : ∀ᶠ j in atTop, ∀ x, ‖g j x‖ ≤ B x:=by
    filter_upwards [H] with i hi x
    by_cases he:x∈Fund C.S p n
    · unfold g B stepping; rw [indicator_of_mem he,indicator_of_mem he]
      let a:= address (C.S.a (e i)) x; let y:= tag (C.S.a (e i)) a; change ‖t y* F (e i) a‖ ≤ _
      rcases eq_or_ne (t y) 0 with H|H
      · rw [H,zero_mul,norm_zero]; exact mul_nonneg hR hD
      exact (norm_mul_le ..).trans (mul_le_mul (hT _) (hi a (subset_closure H)) (norm_nonneg _) hR)
    simp [g,B,stepping,he]
  have he:∀ᵐ x:Points n,Tendsto (fun i=>g i x) atTop (𝓝 (t x*f x)):=by
    filter_upwards [almostCyclic C.S p n] with x hx
    by_cases hp:x∈Fund C.S p n
    · simp_rw [g,stepping,indicator_of_mem hp]; let a j:=address (C.S.a (e j)) x
      have he:= (Extraction.chosen (S:=C.S) x).comp e.cofinal
      have hv : x∈ NoHit C.S p n:= fun i j hij=> ⟨0,hx i j hij 0⟩
      have hr:= h.2 x hv a id tendsto_id he; exact (t.continuous.continuousAt.tendsto.comp he).mul hr
    have hw : t x=0:= by
      by_contra! H
      have hu : x∈ Inside C.S p n:= ht (subset_closure H)
      exact hp (show ∀ i a, _< x i a ∧ x i a ≤ _ from fun i a=> ⟨(hu i a).1,(hu i a).2.le⟩)
    simp_rw [g,stepping,indicator_of_notMem hp,hw,zero_mul]; exact tendsto_const_nhds
  constructor
  · exact hb.mono' (aestronglyMeasurable_of_tendsto_ae atTop hm he) (he.mono fun x hx=> le_of_tendsto hx.norm (hP.mono fun _ hi=> hi x))
  apply (tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall hm)
    (hP.mono fun i H=> Eventually.of_forall H) hb he).congr' (Eventually.of_forall fun i=> (stored ..).2)
end YM.FullVolume
