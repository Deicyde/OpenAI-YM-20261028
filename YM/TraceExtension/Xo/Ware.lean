import YM.TraceExtension.Xo.Lyre
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Xo
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{Y:Gal G n}{P:Support n}
def maroon (G:Gauge)(n:Side)(U:Config G n)(v:Link G n):=input G n v*U
private lemma sun (h:Clouded Y P)(U:Config G n):ContDiffAt ℝ ω (Y ∘ maroon G n U) 0:= h.wakes _ _ _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park _ _))
lemma lushT(h:Clouded Y P)(U:Config G n): lush Y U= (billsM (pocket _) (pocket _) (fderiv ℝ (Y ∘ maroon _ _ U) 0)).trace:=by
    rw [tether Y U (sun h U)]; apply sum_congr rfl fun i _=>?_
    let F:=maroon G n U;let L:Link G n→L[ℝ] ℝ:= ContinuousLinearMap.proj i
    let A:= fderiv ℝ (Y ∘ maroon G n U) 0
    change fderiv ℝ (L ∘ (Y ∘ maroon G n U)) 0 (bolt i)= billsM (pocket _) (pocket _) A i i
    rw [fderiv_comp 0 L.differentiableAt ((sun h U).differentiableAt (by simp)),bill_def,L.fderiv,bockat,cash_pocket];rfl
lemma lushSym(h:Clouded Y P): GaugeInvariant (lush Y):=by
    intro k U; let V:=Lattice.gauge k U; let F:=Y∘maroon G n V;let H:=Y ∘ maroon G n U; let L:= armor k; let A:= billsM (pocket _) (pocket _) (fderiv ℝ F 0); let B:=billsM (pocket _) (pocket _) (fderiv ℝ H 0);let T':=Stationary.trench k
    have hx : F ∘ L=L ∘ H:= funext (fun x=> by
        change Y (input _ _ _*V)=_; rw[armor_go]; exact h.paints ..)
    have hv:A*T'=T'*B:=by
        have hp:= (show F ∘ L=ᶠ[𝓝 0] L ∘ H from hx ▸ EventuallyEq.refl ..).fderiv_eq (𝕜:=ℝ)
        have ht: DifferentiableAt ℝ F (L 0):=by rw[map_zero]; exact (sun h V).differentiableAt (by simp)
        rw[fderiv_comp 0 ht L.differentiableAt,map_zero,L.fderiv,fderiv_comp 0 L.differentiableAt ((sun h U).differentiableAt (by simp)),L.fderiv] at hp
        apply testers; intro x y; unfold A B T'; rw[← mulVec_mulVec,← mulVec_mulVec,bill_pay, show Stationary.trench k*ᵥ y=_ from bill_pay (armor k) y,bill_pay, show Stationary.trench k*ᵥ _=_ from bill_pay ..]; exact congr_arg (dotProduct x) (DFunLike.congr_fun hp y)
    have hz:= trench_orthogonal k; rw[lushT h,lushT h]; change A.trace=B.trace; rw[hz.carry hv, Matrix.trace_mul_comm _ _,← Matrix.mul_assoc,hz.right, Matrix.one_mul]
lemma lushTide (h:Clouded Y P): Drift _ (lush Y) :=by
    rw [funext fun V=> tether Y V (sun h V)]; intro X _ _ W x hp; unfold Function.comp; refine ContDiffAt.sum (fun i _=> ride_sure ?_ i _ W x hp)
    intro V _ _ W y hz; exact (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Lines G n 1=>ℝ) _).contDiff.contDiffAt.comp _ (h.wakes V W y hz)
lemma lushLocales(h: Clouded Y P):LocalOn P (lush Y):=by
    rw [funext fun V=>tether Y V (sun h V)]; intro U V hv; apply Finset.sum_congr rfl fun i _=>?_; exact riddle (fun W T hf=> congr_fun (h.stout W T hf) i) i U V hv
-- useful remove constant then loom.Est payout.
def stubJ (F:Peat G n):Peat G n:=fun U=> F U-F 1
lemma lush_p(h:Clouded Y P)(he:G.Simple): stubJ (lush Y)∈loom G n:= clergyP _ (fun k U=> congr_arg₂ (· - ·) (lushSym h k U) rfl) ((lushTide h _ _ _ (Army.powL (v:=id) contDiffAt_id)).sub contDiffAt_const) (by unfold stubJ; ring) he
lemma lushLine (G:Gauge)(k:ℕ)(A:ℝ)(hA:0≤ A):∃ D:ℝ,0≤ D∧∀ (V:Type) [NormedAddCommGroup V] [NormedSpace ℝ V](n:Side)(Y:Gal G n)(P:Support n)(C:ℝ)(W:V→ Config G n)(x:V), Clouded Y P→ Climate Y k C D→(∀ i, Allows (k+1) (fun v=> G.mat (W v i)) x A)→Allows k (lush Y ∘ W) x ((↑(P.card*Fintype.card (Loc G 1)):ℝ)*C):=by
   obtain ⟨M,hM,H⟩:=pie_roll G (k+1) A hA
   refine ⟨M,hM,?_⟩; intro V _ _ n Y P C W x h hx hh
   let Z(p:V×Link G n):=input G n p.2*W p.1; have hp(i:Lines G n 1): Allows k (fun y=>outD (fun U=>Y U i) i (W y)) x C:= priced_partial (f:=fun p:V×Link G n=>Y (Z p) i) (x:=x) (hx.laps _ Z _ (H _ _ _ hh) i) _ (norm_bolt ..|>.le)
   let S:= P ×ˢ (@univ (Loc G 1) _)
   let f(i:Lines G n 1)(v:V):= outD (fun U=>Y U i) i (W v); have hv(v): (lush Y ∘ W) v=∑ i∈ S,f i v:=by
       rw [Function.comp_apply, tether Y _ (sun h _)]; apply Eq.symm (sum_subset (subset_univ _) ?_); intro i _ hi; rw[show (fun U=>Y U i)=(fun _=>0) from funext fun t=> h.toes _ _ (fun hx=>hi (mem_product.mpr ⟨hx,mem_univ _⟩))]; simp[outD]
   rw[funext hv]; apply (allows_sum (f:=f) (s:=S) (fun i _=>hp i)).mono; simp only[S,sum_const, card_product,card_univ,nsmul_eq_mul]; push_cast; rfl
end YM.Trace.Xo
