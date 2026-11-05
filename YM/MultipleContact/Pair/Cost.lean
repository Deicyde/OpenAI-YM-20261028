import YM.Euclid.Stress
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Local asymptotic norm estimates on punctured Euclidean vector neighborhoods, with uniform compact-parameter constants. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Two
open Function Filter Set Metric Real
open scoped Topology Filter BigOperators Classical

variable {E V F : Type*}[NormedAddCommGroup E][NormedAddCommGroup V][NormedAddCommGroup F]
 {α β : Type*}

abbrev deleted (E:Type*) [TopologicalSpace E][Zero E] := 𝓝[{0}ᶜ] (0:E)

def Asympt (K:Set α) (g:α → E → V)(p:ℝ) : Prop :=
 ∃ c:ℝ, 0≤c ∧ ∀ᶠ y in deleted E, ∀ i∈ K, ‖g i y‖ ≤ c * ‖y‖ ^ p
abbrev LocalBound (g:E→V) (p:ℝ) := Asympt (univ : Set Unit) (fun _ => g) p

variable {K:Set α}{g g':α→E→V}{f:E→V}{p p':ℝ}
namespace Asympt
lemma weaken (h:Asympt K g p') (he:p≤p') : Asympt K g p:=by
  obtain ⟨c,hc,h'⟩:= h
  refine ⟨c,hc,?_⟩
  filter_upwards [self_mem_nhdsWithin (a:=(0:E)) (s:={0}ᶜ),Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:E) one_pos),h'] with y hy hy' hw i hi
  simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hy; rw [dist_zero_right] at hy'
  exact (hw i hi).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hy) hy'.le he) hc)
lemma reindex (h:Asympt K g p) (A:Set β)(u:β→E→α) (hu:∀ᶠ y in deleted E, ∀i∈A, u i y∈ K) : Asympt A (fun i y=>g (u i y) y) p:=by
  obtain ⟨c,hc,hw⟩ :=h; exact ⟨c,hc,(hw.and hu).mono (fun i hi j hj => hi.1 _ (hi.2 j hj))⟩
lemma all (h:LocalBound f p)(A:Set β) : Asympt A (fun _ y=>f y) p:=h.reindex A (fun _ _=>()) (Eventually.of_forall fun _ _ _=>Set.mem_univ _)
lemma congr (h:Asympt K g p)(he:∀ᶠ y in deleted E, ∀i∈K,g i y = g' i y):Asympt K g' p:=by
   obtain ⟨c,hc,h⟩:=h; exact ⟨c,hc,(he.and h).mono (fun i hi j hj => (congr_arg (fun x=> ‖x‖) (hi.1 j hj).symm).le.trans (hi.2 j hj))⟩
lemma sub (h:Asympt K g p)(h':Asympt K g' p):Asympt K (fun i y=>g i y-g' i y) p:=by
   obtain ⟨c,hc,h₀⟩:=h; obtain ⟨c',hc',h'₀⟩:=h'
   refine ⟨c+c',add_nonneg hc hc',(h₀.and h'₀).mono fun y ⟨h₁,h₂⟩ i hi =>?_⟩
   exact (norm_sub_le ..).trans ((add_le_add (h₁ i hi) (h₂ i hi)).trans_eq (add_mul ..|>.symm))
lemma add (h:Asympt K g p)(h':Asympt K g' p):Asympt K (fun i y=>g i y+g' i y) p:=by
   obtain ⟨c,hc,h₀⟩:=h; obtain ⟨c',hc',h'₀⟩:=h'
   refine ⟨c+c',add_nonneg hc hc',(h₀.and h'₀).mono fun y ⟨h₁,h₂⟩ i hi =>?_⟩
   exact (norm_add_le ..).trans ((add_le_add (h₁ i hi) (h₂ i hi)).trans_eq (add_mul ..|>.symm))
lemma zero : Asympt K (fun _ (_:E) => (0:V)) p:=⟨0,le_rfl, Eventually.of_forall (by simp)⟩
lemma finite_sum (I:Finset β) (u:β→α→E→V) (hu:∀i∈I,Asympt K (u i) p):Asympt K (fun i y=>∑ j∈I, u j i y) p:=by
   induction I using Finset.induction_on with
   | empty => simpa using (zero (E:=E) (V:=V) (K:=K) (p:=p))
   | @insert i I hi IH=> simp_rw [Finset.sum_insert hi]; exact (hu i (Finset.mem_insert_self i I)).add (IH fun j hj=>hu j (Finset.mem_insert_of_mem hj))
omit [NormedAddCommGroup F] in
lemma pi {H:β→Type*}[∀i,NormedAddCommGroup (H i)][Fintype β] (g:∀i:β,α→ E→H i)(hg:∀i,Asympt K (g i) p):Asympt K (fun i y j=> g j i y) p:=by
   choose c hc hw using hg
   obtain ⟨C,hC⟩:=Finite.bddAbove_range c
   let a:=max 0 C
   refine ⟨a,le_max_left ..,(eventually_all.mpr hw).mono fun y hh i hi=>?_⟩
   apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_max_left 0 C) (Real.rpow_nonneg (norm_nonneg y) p))).2
   intro j; exact (hh j i hi).trans (mul_le_mul_of_nonneg_right ((hC (Set.mem_range_self _)).trans (le_max_right ..)) (Real.rpow_nonneg (norm_nonneg _) _))

lemma op (h:Asympt K g p) {b:α→E→F} {q C:ℝ} (hC:0≤C)(hw:∀ᶠ y in deleted E,∀ i∈K, ‖b i y‖ ≤ C*‖g i y‖ * ‖y‖^q) : Asympt K b (p+q):=by
  obtain ⟨a,hA,hh⟩:=h
  refine ⟨C*a,mul_nonneg hC hA,?_⟩
  filter_upwards [self_mem_nhdsWithin (a:=(0:E)) (s:={0}ᶜ),hw,hh] with y hy hp hp' i hi
  have h':=hp i hi
  have h₁:=hp' i hi
  have ht:=Real.rpow_nonneg (norm_nonneg y) q
  rw [Real.rpow_add (norm_pos_iff.mpr (fun h=>hy (Set.mem_singleton_iff.mpr h)))]
  exact h'.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hC) ht).trans_eq (by ring))
lemma linear [NormedSpace ℂ V][NormedSpace ℂ F][FiniteDimensional ℂ V](h:Asympt K g p) (b:α→V→ₗ[ℂ] F)(hb:∃C:ℝ, 0≤C ∧ ∀i∈K,∀v,‖b i v‖≤ C*‖v‖) :Asympt K (fun i y=> b i (g i y)) p:=by
  obtain ⟨c,hc,hc'⟩:=hb
  exact Eq.mp (congr_arg _ (add_zero p)) (h.op (q:=(0:ℝ)) hc (b:=fun i y=> b i (g i y)) (Eventually.of_forall fun y i hi=>by simpa using hc' i hi (g i y)))
lemma linear_const [NormedSpace ℂ V][NormedSpace ℂ F][FiniteDimensional ℂ V] (h:Asympt K g p)(w:V→ₗ[ℂ] F):Asympt K (fun i y=>w (g i y)) p:=h.linear (fun _=>w) (by exact ⟨‖LinearMap.toContinuousLinearMap w‖,norm_nonneg _,fun _ _=> (LinearMap.toContinuousLinearMap w).le_opNorm⟩)
end Asympt
lemma norm_eventually (r:ℝ) (hr:0<r) : ∀ᶠ x:E in deleted E, 0< ‖x‖ ∧ ‖x‖<r := by
   filter_upwards [self_mem_nhdsWithin (a:=(0:E)) (s:=({0}ᶜ:Set E)),Filter.Eventually.filter_mono (nhdsWithin_le_nhds (a:=(0:E)) (s:={0}ᶜ)) (ball_mem_nhds (0:E) hr)] with x hx hy
   rw [dist_zero_right] at hy
   exact ⟨norm_pos_iff.mpr (fun he=>hx (Set.mem_singleton_iff.mpr he)),hy⟩
lemma has_radius (p:E→ Prop)(hw:∀ᶠ y in deleted E,p y): ∃r:ℝ,0<r∧∀x:E,0<‖x‖→ ‖x‖ <r → p x:=by
    obtain ⟨r,hr,hR⟩:= Metric.nhdsWithin_basis_ball.mem_iff.mp hw
    exact ⟨r,hr,fun x hx h=>hR (⟨by simpa only [mem_ball,dist_zero_right] using h,by exact fun e=> (norm_pos_iff.mp hx) (Set.mem_singleton_iff.mp e)⟩)⟩
section Map
omit [NormedAddCommGroup V] [NormedAddCommGroup E] [NormedAddCommGroup F] in
lemma linear_bound_compact [TopologicalSpace α] (hK:IsCompact K) {G:Type*}[NormedAddCommGroup G] [ProperSpace G][NormedSpace ℂ G]
   {V':Type*}[NormedAddCommGroup V'][NormedSpace ℂ V'] (f:α→G→ₗ[ℂ] V') (hf : ContinuousOn (fun y:α×G=>f y.1 y.2) (K×ˢ univ)):
   ∃c:ℝ, 0≤c∧∀i∈K,∀g:G,‖f i g‖≤c*‖g‖:=by
   obtain ⟨a,ha⟩:=(hK.prod (isCompact_closedBall (0:G) 1)).bddAbove_image (hf.norm.mono (prod_mono_right (subset_univ _)))
   refine ⟨max 0 a,le_max_left ..,fun i hi g=>?_⟩
   by_cases he:g=0
   · simp [he]
   let v:=((↑(‖g‖):ℂ))⁻¹ • g; have hw:v∈closedBall (0:G) 1:=by
       rw [Metric.mem_closedBall,dist_zero_right,norm_smul,norm_inv,Complex.norm_real, Real.norm_eq_abs,abs_norm,inv_mul_cancel₀ (norm_pos_iff.mpr he).ne']
   calc _ = ‖g‖*‖f i v‖ := by
          have hp:=show (↑‖g‖:ℂ) • v=g from by dsimp only [v];rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast norm_pos_iff.mpr he|>.ne'),one_smul]
          nth_rw 1 [← hp]; rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_norm]
        _ ≤ _:= (mul_le_mul_of_nonneg_left ((ha ⟨(i,v),Set.mem_prod.mpr ⟨hi,hw⟩,rfl⟩).trans (le_max_right ..)) (norm_nonneg g)).trans_eq (mul_comm ..)
-- continuous on a compact:punctured disk of any radius at compact parameters.
variable {f:α → E → V}{K:Set α}[TopologicalSpace α]
lemma repair (hK:IsCompact K)[ProperSpace E](p:ℝ)(h:Asympt K f p)(R:ℝ)(hR:ContinuousOn (fun x:α× E=>f x.1 x.2) (K×ˢ (ball 0 R\ {0})))(r:ℝ)(hr:r<R):
     ∃a:ℝ,0≤a∧∀i∈K,∀x∈closedBall (0:E) r\{0}, ‖f i x‖≤ a * ‖x‖^p:=by
     obtain ⟨C,hC,hc⟩:=h
     obtain ⟨ε,hε,he⟩:=has_radius _ hc
     let L:= K ×ˢ (closedBall (0:E) r \ ball 0 ε)
     have hL:IsCompact L:=hK.prod ((isCompact_closedBall ..).of_isClosed_subset (IsClosed.sdiff isClosed_closedBall isOpen_ball) sdiff_subset)
     have hr': L⊆ K ×ˢ (ball 0 R\{0}) := by refine prod_mono_right (sdiff_subset_sdiff (closedBall_subset_ball hr) (singleton_subset_iff.mpr (mem_ball_self hε)))
     let g(y:α×E):=‖f y.1 y.2‖/‖y.2‖^p
     have hp (y:α×E)(hy:y∈L):0<‖y.2‖:=norm_pos_iff.mpr (fun h=>(Set.mem_prod.mp (hr' hy)).2.2 (Set.mem_singleton_iff.mpr h))
     have hv:ContinuousOn g L:=(hR.norm.mono hr').div (fun y hy=>(continuous_snd.norm.continuousAt.rpow_const (Or.inl (hp y hy).ne')).continuousWithinAt) (fun y hy=>(Real.rpow_pos_of_pos (hp y hy) p).ne')
     obtain ⟨a,ha⟩:= hL.bddAbove_image hv
     refine ⟨max a C,hC.trans (le_max_right a C),fun i hi v hh=>?_⟩
     have hp:0 < ‖v‖ := norm_pos_iff.mpr (fun h=>hh.2 (Set.mem_singleton_iff.mpr h)); have hp':=Real.rpow_pos_of_pos hp p
     by_cases he': ‖v‖ < ε
     · exact (he _ hp he' _ hi).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hp'.le)
     exact ((div_le_iff₀ hp').mp (ha ⟨(i,v),Set.mem_prod.mpr ⟨hi,hh.1,by simpa only [mem_ball,dist_zero_right] using he'⟩,rfl⟩)).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hp'.le)
end Map
end YM.MultipleContact.Two
