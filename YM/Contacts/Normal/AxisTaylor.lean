import YM.Contacts.Normal.TestRates

/-! # Parameter Taylor proof with full derivative bounds in *other* variables -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Set Metric MeasureTheory Submodule MultipleContact Panel
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (K : Submodule ℝ E) {i j n m : ℕ} {T : Set E} {g : E×ℝ → ℂ} {r B : ℝ}

variable (E) in
def horizontal : Lens (E × ℝ) E:= ⟨ContinuousLinearMap.fst _ _ _, ContinuousLinearMap.inl _ _ _,fun _=>rfl⟩
variable (E) in
def vertical : Lens (E × ℝ) ℝ:= ⟨ContinuousLinearMap.snd _ _ _, ContinuousLinearMap.inr _ _ _,fun _=>rfl⟩
local notation "V" => vertical E
local notation "L" => horizontal E
omit [FiniteDimensional ℝ E]
@[simp] lemma hslice (x : E) (t : ℝ) (f : E × ℝ → ℂ) (y : E) : (horizontal E).slice (x,t) f y= f (y,t):= by
   unfold Lens.slice Lens.lay Lens.off; change f ((y,0)+((x,t)-(x,0)))=_; rw [Prod.mk_sub_mk, Prod.mk_add_mk]; simp
@[simp] lemma vslice (x : E) (t : ℝ) (f : E × ℝ → ℂ) (s : ℝ) : (vertical E).slice (x,t) f s= f (x,s):= by
   unfold Lens.slice Lens.lay Lens.off; change f ((0,s)+((x,t)-(0,t)))=_; rw [Prod.mk_sub_mk, Prod.mk_add_mk]; simp
lemma hadamard (q : Fin j→ E) : ((List.ofFn (fun i=>(L).put (q i))).map (‖·‖)).prod = ∏ i : Fin j, ‖q i‖ := by
  rw [List.map_ofFn,List.prod_ofFn]; apply Finset.prod_congr rfl; intro i hi; change ‖(q i,(0:ℝ))‖=_; simp
lemma equalized (h : ContDiff ℝ ∞ g)(x : E)(t : ℝ)(q : Fin j → E) :
    (iteratedFDeriv ℝ j (fun x=>g (x,t)) x) q= blades (List.ofFn (fun i=> (horizontal E).put (q i))) g (x,t) := by
   rw [blades_eval h,← funext (hslice x t g), (horizontal E).slice_deriv j _ h]; congr; exact Lens.lay_read L _ -- `congr` 
lemma slice_bill (h : ContDiff ℝ ∞ g)(U : Set ℝ) (t : ℝ) (k : Jet n (T ×ˢ U) g r)(ht : t∈U) : Jet n T (fun x=>g (x,t)) r:= by
   refine ⟨k.pos,fun j hj x hx=>?_⟩; refine ContinuousMultilinearMap.opNorm_le_bound k.pos fun q=>?_ ; rw [equalized h]; exact (k.priceBlade _ h (by simpa using hj) ⟨hx,ht⟩).trans_eq (by rw [hadamard])

lemma vertical_blades (g : E×ℝ→ℂ)(h : ContDiff ℝ ∞ g)(q : Fin j → E) (n : ℕ) : blades (List.ofFn (fun i=>(horizontal E).put (q i))) ((vertical E).atom n g)= (vertical E).atom n (blades (List.ofFn (fun i=>(horizontal E).put (q i))) g) := by
  have he (w : List (E × ℝ)) (hv : ∀ v∈w, (vertical E).read v=0) : blades w ((vertical E).atom n g)= (vertical E).atom n (blades w g):= by
    induction w with
    | nil=> rfl
    | cons v w ih=> change blade v (blades w ((vertical E).atom n g))= _; rw [ih (List.forall_mem_cons.mp hv).2]; exact (vertical E).blade_atom v (List.forall_mem_cons.mp hv).1 _ (blades_smooth h w) n
  exact he _ fun _ hw=> by obtain ⟨i,rfl⟩:= List.mem_ofFn.mp hw; rfl
lemma vertical_blades_sum (g : E×ℝ→ℂ)(h : ContDiff ℝ ∞ g)(q : Fin j→ E)(n : ℕ) : blades (List.ofFn (fun i=> (horizontal E).put (q i))) ((vertical E).atoms n g)= (vertical E).atoms n (blades (List.ofFn (fun i=>(horizontal E).put (q i))) g):=by
  funext x; unfold Lens.atoms; rw [blades_sum (w:=Finset.range (n+1)) (fun i=>(vertical E).atom i g) (fun i=>Lens.atom_smooth _ i h)]; simp_rw [vertical_blades g h q]

/-- Scalar channel estimate after spatial blade derivatives. No symmetry assumed of test; spend
spatial/normal-param derivatives at the same time. -/
lemma mixed_bill (g : E×ℝ→ℂ)(h : ContDiff ℝ ∞ g)(q : Fin j → E) {x : E}{t u : ℝ}{U : Set (E×ℝ)} (H : Jet n U g r) (hj : i+j ≤ n)
     (hx : (x,t) ∈ U) : ‖iteratedFDeriv ℝ i (fun s=>blades (List.ofFn (fun k=>(horizontal E).put (q k))) g (x,s)) t (fun _=>u)‖ ≤ r * |u|^i * ∏ k,‖q k‖:= by
   let p:=List.ofFn (fun k=>(horizontal E).put (q k)); change ‖iteratedFDeriv ℝ i (fun s=>blades p g (x,s)) _ _‖≤_
   rw [← funext (vslice x t (blades p g)), (vertical E).slice_deriv i _ (blades_smooth h _), ← blades_eval (blades_smooth h _),← blades_join]; let s:=List.ofFn (fun _:Fin i=> (vertical E).put u)
   have ht := (H.priceBlade (s++p) h (by simpa [s,p]) hx); rw [show (vertical E).lay (x,t) t=(x,t) from (vertical E).lay_read (x,t)]; refine ht.trans_eq ?_; unfold s p; rw [List.map_append,List.prod_append,hadamard,List.map_ofFn,List.prod_ofFn]
   change r * ((∏ _:Fin i,‖((0:E),u)‖)*_)=_
   simp_rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg u), Finset.prod_const, Finset.card_univ,Fintype.card_fin, Real.norm_eq_abs,mul_assoc]

lemma vat (g : E×ℝ→ℂ)(h : ContDiff ℝ ∞ g)(x : E)(t : ℝ) (i : ℕ) : (vertical E).atom i g (x,t)= coeff i (fun s=>g (x,s)) t:= by
   unfold Lens.atom; unfold coeff; rw [← funext (vslice x t g), (vertical E).slice_deriv i _ h,Lens.lay,map_zero,zero_add]; rfl
lemma vjet (g : E×ℝ→ℂ)(h : ContDiff ℝ ∞ g)(x : E)(t : ℝ) (n : ℕ) : (vertical E).atoms n g (x,t)=polyJet n (fun s=>g (x,s)) t:= Finset.sum_congr rfl fun _ _=> vat g h x t _

lemma axis_piece_budget (h : ContDiff ℝ ∞ g)(U : Set ℝ) (H : Jet n (T ×ˢ U) g r) (i j : ℕ) (hj : i+j ≤ n) (hu : 0∈ U) (a : ℝ) : Jet j T (fun x=> (vertical E).atom i g (x,a)) (r*|a| ^ i):= by
   have hp := H.pos; refine ⟨by positivity,fun k hk x hx=>?_⟩; apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro q
   rw [equalized (Lens.atom_smooth V i h), vertical_blades g h q, vat _ (blades_smooth h _)]
   apply fact_mul_bound.trans (mixed_bill g h q H (by omega) ⟨hx,hu⟩)
lemma axis_remainder (h : ContDiff ℝ ∞ g)(U : Set ℝ) (H : Jet n (T ×ˢ U) g r) (i j : ℕ)(hj : (i+1)+j≤ n) (a : ℝ) (ha : 0 ≤ a) (he : Icc 0 a ⊆ U) : Jet j T (fun x=> (g-(vertical E).atoms i g) (x,a)) (r*a^(i+1)):=by
   have hp:= H.pos; refine ⟨by positivity,fun k hk x hx=>?_⟩; apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro q
   let w := List.ofFn (fun l=> (horizontal E).put (q l)); have hw : ContDiff ℝ ∞ ((vertical E).atoms i g):=ContDiff.sum (fun n _=>Lens.atom_smooth V n h)
   rw [equalized (show ContDiff ℝ ∞ (g-(vertical E).atoms i g) from h.sub hw), blades_sub h hw, vertical_blades_sum g h q]
   let p(t:ℝ):= blades w g (x,t); change ‖p a- (vertical E).atoms i (blades w g) (x,a)‖ ≤_
   have hP : ContDiff ℝ ∞ p:= (blades_smooth h w).comp (contDiff_const.prodMk contDiff_id)
   rw [vjet _ (blades_smooth h _)]
   change ‖p a-polyJet i p a‖ ≤ _; nth_rw 1 [poly_integral hP i a]; rw [add_sub_cancel_left]; apply fact_mul_bound.trans; refine (intervalIntegral.norm_integral_le_of_norm_le_const (C:=r*a^(i+1)*∏ z,‖q z‖) ?_).trans (by norm_num)
   intro t ht; have ht : t ∈ Ioc 0 1:= by rwa [uIoc_of_le zero_le_one] at ht
   let y:= iteratedFDeriv ℝ (i+1) p (t • a) (fun _=>a); change ‖_ • y‖≤_; have h₂ : ‖y‖ ≤ r* |a| ^(i+1)*∏ z, ‖q z‖:= mixed_bill g h q H (by omega) ⟨hx, he ⟨mul_nonneg ht.1.le ha, mul_le_of_le_one_left ha ht.2⟩⟩; rw [abs_of_nonneg ha] at h₂
   rw [norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) h₂
   rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
   apply pow_le_one₀ (sub_nonneg.mpr ht.2) (sub_le_self _ ht.1.le)
end YM.Contacts.Normal
