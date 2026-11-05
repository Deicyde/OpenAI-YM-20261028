import YM.OPE.Orbits.Average

/-!
Physical reality and spatial symmetries of finite readouts `checkReal`, exact
within their domains independently of comparison estimates. The other
parameter here named `d` is a VECTOR of input horizons, not the degree of an
abstract Fock model. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter Set MeasureTheory Extraction Table Word Prescription
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
attribute [local instance] measO
variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{P:Prescription Q}{X:Rotation S}{ρ:S.RealSpin}
    {I:Type}[Fintype I] {d:I→ℕ} (m:ℕ)

def conjugateR (ρ:S.RealSpin)(m:ℕ): S.Field m→ₗ[ℝ] S.Field m where
  toFun := S.conj ρ m
  map_add' := map_add _
  map_smul' r x:= by
       change S.conj ρ m (r • x)=r • S.conj ρ m x
       simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]; simp
variable (hX:X.Laws Q ρ)(hS:S.Hierarchy) (x:I→E4)(o:E4)

def barRow :MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field m) :=by
    classical
    let F := readMap (d:=d) P X hX hS m x o
    refine ⟨fun v=>S.conj ρ m (F (bar ρ v)),?_,?_⟩
    all_goals
       intro k; cases Subsingleton.elim k (Classical.decEq _)
       have hh (v:Labels S d)(i:I) (a:S.Field (d i)) : bar ρ (update v i a)=update (bar ρ v) i (S.conj ρ _ a):=by
          funext j; by_cases he:j=i; subst j; · rw [update_self]; exact congr_arg _ (update_self i a v)
          rw [update_of_ne he]; exact congr_arg (fun z=>S.conj ρ _ z) (@update_of_ne I (S.Field ∘ d) _ j i he a v) -- check
    · intro v z a b; rw [hh,hh,hh,map_add,F.map_update_add,map_add]
    intro v i a b; rw [hh,hh,map_smulₛₗ, F.map_update_smul,map_smulₛₗ]; simp

def checkReal (P:Prescription Q) {X:Rotation S}{ρ:S.RealSpin}(hX:X.Laws Q ρ)
    (hS:S.Hierarchy)(m:ℕ)(x:I→E4)(o:E4): MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field m) :=
        (2:ℂ)⁻¹ • (readMap P X hX hS m x o + barRow (P:=P) m hX hS x o)

variable (v:Labels S d)
include hX hS
lemma checkValue: checkReal P hX hS m x o v=(2:ℝ)⁻¹ • (averageV P X m x o v+S.conj ρ m (averageV P X m x o (bar ρ v))):=by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; simp only [RCLike.ofReal_inv,RCLike.ofReal_ofNat]; rfl

omit hS hX in
lemma permMargin {J:Type}[Fintype J](e:J≃I): orbitMargin P m (x ∘ e) o ↔ orbitMargin P m x o:=by
   have he(k:Ortho)(i:Exterior L): beside (away (Ortho.move k ∘ (x ∘ e)) (Ortho.move k o)) (bearing i)= beside (away (Ortho.move k ∘ x) (Ortho.move k o)) (bearing i) ∘ Equiv.sumCongr e (Equiv.refl _):=by funext j; cases j<;> rfl
   unfold orbitMargin Dock; simp_rw [he]; constructor
   · intro h i hv k p hp; have hh:=h i hv k p hp
     let F:=Equiv.sumCongr e (Equiv.refl (Fin p.n))
     intro a b he; apply F.symm.injective; refine hh (a₁:=F.symm a) (a₂:=F.symm b) ?_; change beside _ _ (F (F.symm a))=beside _ _ (F (F.symm b)); simpa
   exact fun h i hi k p he=> (h i hi k p he).comp (Equiv.injective _)

omit hX hS in
lemma translateMargin (b:E4):orbitMargin P m (fun i=> x i+b)  (o+b)↔ orbitMargin P m x o:=by
    have he (k:Ortho): (away (Ortho.move k ∘ (fun i=> x i+b)) (Ortho.move k (o+b)))= away (Ortho.move k ∘ x) (Ortho.move k o):=funext fun j=>by unfold away; change Ortho.motion k (x j+b) - Ortho.motion k _=_; rw [map_add,map_add,add_sub_add_right_eq_sub]; rfl
    unfold orbitMargin Dock; simp_rw [he]
omit hX in
private lemma average_perm {J:Type}[Fintype J] (e:J≃I): averageV P X m (x ∘ e) o (d:=d ∘ e) (fun j=> v (e j)) = averageV P X m x o v:=by
   classical
   have hf(k:Ortho)(a:Mode Q): P.ope a (Ortho.move k⁻¹ ∘ (x ∘ e)) (names (d:=d ∘ e) (roll X k⁻¹ (fun j=>v (e j) : Labels S (d ∘ e)))) (Ortho.move k⁻¹ o)=P.ope a (Ortho.move k⁻¹ ∘ x) (names (roll X k⁻¹ v)) (Ortho.move k⁻¹ o):= by apply P.coefficient_perm (x:=Ortho.move k⁻¹ ∘ x) (names (roll X k⁻¹ v)) hS.laws.toSymmetric e
   unfold averageV; rw [permMargin m x o e]; split; swap; rfl
   refine integral_congr_ae (Eventually.of_forall fun k=>congr_arg (X.act _ k) ?_)
   unfold shadow; exact Finset.sum_congr rfl (fun a _=> congr_arg (· • P.loaded a _) (hf k a))


lemma checkReal_perm {J:Type}[Fintype J] (e:J≃I): checkReal P hX hS m (x ∘ e) o (d:=d ∘ e) (fun j=> v (e j)) = checkReal P hX hS m x o v:=by
   rw [checkValue,checkValue,average_perm _ hS x o v e]; rw [(show bar ρ (d:=d ∘ e) (fun j=> v (e j))=fun j=> bar ρ v (e j) from rfl)]; apply congr_arg ((2:ℝ)⁻¹ • ·) (congr_arg (_+·) (congr_arg (S.conj ρ m) (average_perm m hS x o (bar ρ v) e)))
omit hX hS in
private lemma coeff_transfer (a:E4)(k:Ortho)(i:Mode Q)(v:I→L.Token): P.ope i (Ortho.move k ∘ (fun i=>x i+a)) v (Ortho.move k (o+a))=P.ope i (Ortho.move k ∘ x) v (Ortho.move k o):=by
   rw [(show Ortho.move k ∘ (fun i=>x i+a)=fun i=>(Ortho.move k ∘ x) i+Ortho.move k a from funext fun i=>map_add (Ortho.motion k) _ _), (show Ortho.move k (o+a)=_ from (Ortho.motion k).map_add _ _)]; apply Prescription.term_carry v (Ortho.move k a)
omit hX hS in
private lemma translate_avg (b:E4): averageV P X m (fun i=>x i+b) (o+b) v=averageV P X m x o v:=by
   unfold averageV; rw [translateMargin]; split; swap; rfl
   refine integral_congr_ae (Eventually.of_forall fun k=> congr_arg (X.act _ k) ?_); unfold shadow; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [coeff_transfer]
lemma checkReal_transfer (s:E4): checkReal P hX hS m (fun i=> x i+s) (o+s) v=checkReal P hX hS m x o v:=by rw [checkValue,checkValue,translate_avg,translate_avg]

lemma checkReal_real : checkReal P hX hS m x o (bar ρ v)=S.conj ρ m (checkReal P hX hS m x o v):=by
   rw [checkValue,checkValue,bar_bar, (show S.conj ρ m ((2:ℝ)⁻¹ • (_+_)) =_ from (conjugateR ρ m).map_smul ..), map_add]; change (2:ℝ)⁻¹ • (_+ _) = 2⁻¹ • (S.conj ρ m _ + S.conj ρ m _); rw [Table.reflect_star,add_comm]
lemma checkReal_fixed (j:ℕ)(u:S.Field j)(hP:P.Coherent)(hQ:Q.Inclusions S)
      (hc:Q.Orientation ρ)(he:j ≤ m) : checkReal P hX hS m (sole 0) 0 (d:=fun _:Unit=>j) (sole u)=Q.rise he u:=by
    have hh:bar ρ (d:=fun _:Unit=> j) (sole u) = sole (S.conj ρ j u):=rfl
    rw [checkValue,hh,average_fixes hX hS m _ hQ hP he,average_fixes hX hS m _ hQ hP he,hc.realInc,S.reflect_star, ← two_smul ℝ, inv_smul_smul₀ (two_ne_zero (α:=ℝ))] -- two_smul names?
lemma checkReal_rotate (k:Ortho): checkReal P hX hS m (Ortho.move k ∘ x) (Ortho.move k o) (roll X k v)=X.act m k (checkReal P hX hS m x o v):=by
    have hr:bar ρ (d:=d) (roll X k v)=roll X k (bar ρ v):=funext (fun i=> by exact hX.real ..)
    rw [checkValue,checkValue,hr,average_rotation hX,average_rotation hX, hX.real]
    rw [show X.act m k _= (2:ℝ)⁻¹ • ((X.act m k).toLinearMap (_+_)) from (X.act m k).toLinearMap.map_smul_of_tower ..,map_add]; rfl
lemma smoothReal (hx:orbitMargin P m x o): ContDiffAt ℝ ∞ (fun t:(I→E4)×E4=>checkReal P hX hS m t.1 t.2 v) (x,o):=by
    simp_rw [checkValue]; exact contDiffAt_const.smul (𝕜':=ℝ) ((average_smooth hX hS m v hx).add ((LinearMap.toContinuousLinearMap (conjugateR ρ m)).contDiff.contDiffAt.comp _ (average_smooth hX hS m (bar ρ v) hx))) -- smul notation
end YM.OPE.Orbits
