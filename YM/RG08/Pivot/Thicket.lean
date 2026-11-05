import YM.RG08.Pivot.Gold

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Planned.PrimaryIntegral295
open scoped Topology BigOperators Classical
variable {G : Gauge} {E : Type} {R : ℝ} {r j n D d : ℕ} {U V : EnvelopeU D R G r}

lemma Sober.harmonic (hF : Sober U) (h : Polished U) (m : Side) (o : Site m) (φ : Exam D) (a : Fin r) (w : Fin r→Link G m)
    (g : Loc G 1→ℝ) (hv : ∀ (p: Site m)(b:Loc G 1), w a (p,b)=g b) : recitalP U o φ w=0 := by
  let f (i:Fin r) (x : Cover × Loc G 1):= w i (o+wrap m x.1,x.2); let P (x : Cover×Loc G 0):=∑ i : Axis,(x.1 i:ℝ)*g (axisEquiv i,x.2.2)
  have hh : f a=polarP P := by
    funext x; rcases x with ⟨x,y,b⟩; obtain ⟨k,rfl⟩:=axisEquiv.surjective y; unfold f polarP P
    dsimp only; rw [hv,← Finset.sum_sub_distrib,Finset.sum_eq_single k]
    · rw [axisEquiv.symm_apply_apply]; simp; ring
    · intro i _ hi; simp [show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _,hi]
    simp
  have he (x) : ‖P x‖≤ ((Fintype.card Axis:ℝ)*‖g‖)*dime 1 x.1:= by
    unfold P; refine (norm_sum_le ..).trans ?_
    apply le_trans (Finset.sum_le_sum (g:=fun _=>‖g‖*dime 1 x.1) ?_)
    · simp [mul_assoc]
    intro i _; rw [norm_mul,mul_comm]; refine mul_le_mul (norm_le_pi_norm g _) ?_ (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs,abs_nat]; unfold dime Carrier.liftCost; rw [pow_one]
    exact le_trans (show _ ≤ (((size x.1):ℕ):ℝ) by exact_mod_cast Finset.single_le_sum (f:=fun i => (x.1 i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ _)) (le_add_of_nonneg_left zero_le_one)
  unfold recitalP; rw [stitch_apply ((polished_pens (polished_fun h (plug φ R))).of_norm)]; exact hF.cover_phi h a P hh (by positivity) he (b:=fun i=>‖w i‖) (fun i=> norm_nonneg _) (fun i p=> le_trans (norm_le_pi_norm (w i) _) (le_mul_of_one_le_right (norm_nonneg _) (Carrier.liftCost_ge ..)))
lemma Sober.static (hk : 0 < R) (hn : 4 ≤ j) {vG : ℝ} {W : EnvelopeU D vG G r} (h : Sober W) (hp : Polished W) (m : Side) (ψ : Exam D) (a : Fin r)
    (s : Train j)(n : Site m)(x : Link G m) (f : Fin r → Link G m) :
    let M:= tensor G (bedtime R s m); let H:=tensor G (Precision.K ((pink R s).acts m)); recitalP W n ψ (update f a ((M*H)*ᵥ x))= recitalP W n ψ (update f a x) := by
  intro M H
  obtain ⟨J,hJ⟩:= eminence G m s hk hn
  let U:= tensor G (haloMat m)
  have hh : ∀ (p z:Site m) (b:Loc G 1),(U*ᵥ x) (p,b)=(U*ᵥ x) (z,b):= fun p z b=> Finset.sum_congr rfl fun i _ => congr_arg (·*x i) (daytime ..)
  have hv := h m n ψ a (update f a (gradient (J*ᵥ x))) (J*ᵥ x) (update_self ..)
  have ht := h.harmonic hp m n ψ a (update f a (U*ᵥ x)) (fun i=> (U*ᵥ x) (0,i)) (fun p b=> by rw [update_self,hh p 0])
  have heq: (M*H)*ᵥ x=x-(gradient (J*ᵥ x)+U*ᵥ x) := by rw [gradient,mulVec_mulVec,← add_mulVec, show _+U= _ from hJ.symm]; rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_sub_cancel]
  rw [heq,(recitalP W n ψ).map_update_sub,(recitalP W n ψ).map_update_add,hv,ht]; simp

lemma gold_scale (h : Gold U) (x : ℝ) : Gold (x • U) := by
  refine ⟨tot_weight h.toToute x,fun m o φ i f g hv=>?_⟩; unfold recitalP; rw [show plug φ R∘ (x•U)= x • (plug φ R ∘ U) from funext fun _=>by simp,
    st_scale x ((h.pens.shaped (plug φ R)).of_norm),_root_.smul_apply]; change x • recitalP U o φ f=0; rw [h.lucid _ _ _ _ _ _ hv,smul_zero]
lemma gold_more (h:Gold U)(hp: Gold V) : Gold (U+V) := by
    refine ⟨tot_more h.toToute hp.toToute,fun m o φ i f g hv=>?_⟩; unfold recitalP; rw [show plug φ R ∘ (U+V)=(plug φ R∘U)+(plug φ R∘V) from funext fun i=>map_add ..,
     st_plus ((h.pens.shaped (plug φ R)).of_norm) ((hp.pens.shaped (plug φ R)).of_norm),_root_.add_apply]; change recitalP U o φ f + recitalP V o φ f=0; rw [h.lucid _ _ _ i f g hv,hp.lucid _ _ _ i f g hv,add_zero]
lemma gold_less (h:Gold U)(hp:Gold V): Gold (U-V) := by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact gold_more h (gold_scale hp _)
lemma gold_home : Gold (0:EnvelopeU D R G r) := by refine ⟨tot_zero,fun m o φ i f _ _=>?_⟩; unfold recitalP; rw [show plug φ R ∘ (0:EnvelopeU D R G r)=(0:Shale _ _) from funext fun _=>map_zero _,st_zero]; rfl
lemma gold_sum {a : Finset E} {U:E→EnvelopeU D R G r} (h : ∀ i∈a,Gold (U i)): Gold (∑ i∈a,U i) := by
  induction a using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact gold_home
  | insert i a hi ih=> rw [Finset.sum_insert hi]; exact gold_more (h i (Finset.mem_insert_self ..)) (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
end YM.RG08.Pivot
