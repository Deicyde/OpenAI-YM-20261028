import YM.Next.MAXWELL.Hidden
import YM.Next.MAXWELL.Magnitude
import YM.Work.A06


/-!
# Real collinear scenes detect the vector's global charge

Route each strict target to an allowed testing line with straight
segment inside conf, monotone preordering ties as needed to preserve
spacing condition (distinct, not a uniform lower bound separate from
the inf of this segment). Only need nonempty axis choice transverse to
the component being tested.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick Climb Ward
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {j k n d : ℕ}

lemma lenses (v : Fin n → (Model F).Field d) (Q : Climb.Matrix d (d+1) (Model F)) :
    AnalyticOnNhd ℝ (diagram v Q) (conf _) := by
  unfold diagram; intro x hx
  apply ContDiffAt.analyticAt
  apply ContDiffAt.sum; intro i _
  unfold Ward.disc; simp_rw [display]; exact kernel_analytic _ hx

private lemma tiesAway (p : Fin n → ℝ) : ∃ q : Fin n → ℝ,Injective q ∧ ∀ i j,p i<p j→ q i<q j := by
  classical
  let f (i : Fin n) t := p i+t*i.val
  have ht (i : Fin n) : Tendsto (f i) little (𝓝 (p i)) := by
    have hv := (show Tendsto id little (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).mul_const ((i.val:ℝ))
    simpa [f] using (tendsto_const_nhds (x:=p i)).add hv
  have hh i j : ∀ᶠ t in little,p i<p j→ f i t<f j t := by
    by_cases h:p i<p j
    · simp only [h,true_imp_iff]; exact (ht i).eventually_lt (ht j) h
    simp [h]
  have hk : ∀ᶠ t in little,∀ i j,p i < p j → f i t<f j t := eventually_all.mpr fun i => eventually_all.mpr fun j=>hh i j
  obtain ⟨t,h,hT⟩ := (hk.and (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0))).exists
  refine ⟨fun i=> f i t,fun i j => ?_,h⟩
  intro he
  rcases lt_trichotomy (p i) (p j) with H|H|H
  · exact ((h i j H).ne he).elim
  · dsimp only [f] at he; rw [H] at he
    apply Fin.ext; exact_mod_cast (mul_left_cancel₀ (show t≠0 from (show t>0 from hT).ne') (add_left_cancel he))
  exact ((h j i H).ne he.symm).elim

private lemma to_scanner {x : Points n} (hx : x∈conf _) (a : Axis) : ∃ y∈conf n,onLine a y ∧ segment ℝ y x ⊆ conf _ := by
  obtain ⟨p,hp,hA⟩ := tiesAway (fun i => x i a)
  let y := points fun i => p i • basis a
  have he : y∈conf n := fun i j h => hp (smul_left_injective ℝ (show basis a≠0 from norm_ne_zero_iff.mp (by simp)) h)
  refine ⟨y,he,fun i => ⟨p i,rfl⟩,?_⟩
  rintro z ⟨u,t,hu,hW,h,rfl⟩
  by_cases ho : u=0
  · rw [ho,zero_add] at h; rw [ho,h,zero_smul,one_smul,zero_add]; exact hx
  by_cases hv : t=0
  · rw [hv,add_zero] at h; rw [hv,h,zero_smul,one_smul,add_zero]; exact he
  have hh (i : Fin n) : (u • y+t • x) i a = u*p i+t*x i a := by simp [y]
  intro i j hi
  have ht : (u • y+t • x) i a=(u • y+t • x) j a := congr_arg (fun x : E4 => x a) hi
  rw [hh,hh] at ht
  rcases lt_trichotomy (x i a) (x j a) with H|H|H
  · have h := hA i j H
    exact ((add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h (lt_of_le_of_ne hu (Ne.symm ho))) (mul_le_mul_of_nonneg_left H.le hW)).ne ht).elim
  · rw [H] at ht; exact hp (mul_left_cancel₀ ho (add_right_cancel ht))
  have h := hA j i H
  exact ((add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h (lt_of_le_of_ne hu (Ne.symm ho))) (mul_le_mul_of_nonneg_left H.le hW)).ne ht.symm).elim

lemma scenes_gone (t : Vector d (Model F)) : (∀ s : Scene (Model F) d, s.lens t=0) ↔ quiet F t := by
  constructor
  · intro v n a p x hx
    obtain ⟨b,hb⟩ := exists_ne a
    obtain ⟨y,hy,hA,h⟩ := to_scanner hx b
    let f := diagram p (t a)
    have hh (m) (B : Fin m → Points n) : iteratedFDeriv ℝ m f y B=0 := v ⟨n,p,b,a,hb.symm,y,hy,hA,m,B⟩
    have hg : f =ᶠ[𝓝 y] 0 := by
      obtain ⟨P,r,hP⟩ := lenses F p _ y hy
      have hw : Tendsto (fun z : Points n => z-y) (𝓝 y) (𝓝 0) := by
        simpa only [id_eq,sub_self] using (tendsto_id (x:=𝓝 y)).sub (tendsto_const_nhds (x:=y))
      filter_upwards [hw.eventually (Metric.eball_mem_nhds _ hP.r_pos)] with z hz
      change z-y ∈ Metric.eball _ _ at hz
      have hl := hP.hasSum_iteratedFDeriv hz
      change HasSum (fun i => ((↑(i.factorial):ℝ)⁻¹) • iteratedFDeriv ℝ i f y fun _=> z - y) _ at hl
      simp_rw [hh,smul_zero,add_sub_cancel] at hl
      exact hl.unique hasSum_zero
    exact ((lenses F p _).mono h).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_segment .. |>.isPreconnected) (left_mem_segment ..) hg (right_mem_segment ..)
  intro H s
  have h : diagram s.v (t s.b)=ᶠ[𝓝 s.x] 0 := (show EqOn _ _ (conf s.n) from fun x hx => H _ _ _ _ hx).eventuallyEq_of_mem ((conf_open _).mem_nhds s.strict)
  unfold Scene.lens; rw [(h.iteratedFDeriv ℝ s.m).eq_of_nhds, iteratedFDeriv_zero]; rfl

lemma finite_lenses (d : ℕ) : ∃ L : Select (standard F) d, ∀ t,L.reads t=0 ↔ quiet F t := by
  classical
  let K s := LinearMap.ker (Work.A06.lensL (S:=Model F) (d:=d) (hierarchy F) s).toLinearMap
  let V (S : Finset (Scene (Model F) d)) := ⨅ s∈ S,K s
  let R k : Prop := ∃ S : Finset (Scene (Model F) d),Module.finrank ℝ (V S)=k
  have hr : ∃ k,R k := ⟨_,∅,rfl⟩
  obtain ⟨S,hS⟩ : R (Nat.find hr) := Nat.find_spec hr
  have he : V S= ⨅ s, K s := by
    apply le_antisymm
    · apply le_iInf; intro s
      have ht : V (insert s S) ≤ V S := by
        unfold V; apply le_iInf; intro i; apply le_iInf; intro h
        exact iInf₂_le i (Finset.mem_insert_of_mem h)
      have hs := Nat.find_min' hr (show R _ from ⟨insert s S,rfl⟩)
      have hz : V (insert s S)=V S := Submodule.eq_of_le_of_finrank_le ht (hS ▸ hs)
      rw [← hz]; exact iInf₂_le s (by simp)
    exact le_iInf fun a => le_iInf fun _ => iInf_le K a
  let e := Fintype.equivFin ↥S
  let s (i) : Scene (Model F) d := (e.symm i).val
  let h := hierarchy F
  let L : V0 (standard F) d →L[ℝ] (Fin (Fintype.card ↥S) → ℂ) := ContinuousLinearMap.pi fun i => Work.A06.lensL h (s i)
  let P : Select (standard F) d := { m := Fintype.card ↥S, rows := s, reads := L, stimulated := fun i p => rfl }
  refine ⟨P,fun t => (Iff.trans ?_ (scenes_gone F _))⟩
  change Vector d (Model F) at t
  constructor
  · intro ht k
    have hv : t∈ V S := by
      unfold V; rw [Submodule.mem_iInf]; intro r; rw [Submodule.mem_iInf]; intro h
      let i : ↥S := ⟨r,h⟩
      rw [← show s (e i)=r by simp [s,i]]; exact congr_fun ht (e i)
    rw [he, Submodule.mem_iInf] at hv; exact hv k
  intro ht; exact funext fun i => ht _

lemma scanner (h : G.Simple) : ∃ N,∀ d≥N,∃ P : Select (standard F) d, Ens P (scheme F) (hierarchy F).spin := by
  obtain ⟨d,H⟩ := exposed h
  refine ⟨max d 4,fun j hj => ?_⟩
  obtain ⟨A,hA⟩ := finite_lenses F j
  have hp : 4≤j := le_trans (le_max_right ..) hj
  have hu : d≤j := le_trans (le_max_left ..) hj
  exact ⟨A,(native (scheme F) (hierarchy F) (scheme_filters F) (scheme_derives F) (phase_orientation F)).sight j,born h F hp,
    fun t v => (hA t).trans (charges_quiet F h hp (fun w p hp h => H _ _ hp (ghost_le hu h)) t v)⟩
end YM.Maxwell.Free
