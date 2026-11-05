import YM.RG08.Trill.Trell
/-! # FD tariff for polynomial probes (including quantitative inverse at first Hol grade).
 Uniform projected bound at arbitrarily high power. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Submodule
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k:ℕ}{σ B:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
variable {U:Type}[AddCommGroup U][Module ℝ U][FiniteDimensional ℝ U] {I:Type}(P:I→Module.Dual ℝ U){g:Module.Dual ℝ U}
lemma jury (H:∀ v:U,(∀ t,P t v=0)→ g v=0):g ∈ Submodule.span ℝ (Set.range P):=by
 let S:=Submodule.span ℝ (Set.range P)
 change g∈S;rw [←Subspace.dualCoannihilator_dualAnnihilator_eq (W:=S)]
 apply (Submodule.mem_dualAnnihilator _).mpr;intro x hx
 unfold S at hx; rw [←SetLike.mem_coe,Submodule.coe_dualCoannihilator_span] at hx
 exact H x fun t=>hx _ ⟨t,rfl⟩
lemma court (H:∀ v:U,(∀ t,P t v=0)→ g v=0)(W:I→ℝ):∃ C:ℝ,0≤C∧∀(B:ℝ)(x:U),0≤B→(∀t,|P t x|≤W t*B)→|g x|≤C*B:=by
 let t(g:Module.Dual ℝ U)(_:g∈Submodule.span ℝ (Set.range P)):=∃ C:ℝ,0≤C∧∀(B:ℝ)(x:U),0≤B→(∀t,|P t x|≤W t*B)→|g x|≤C*B
 refine Submodule.span_induction (p:=t) ?_ ⟨0,le_rfl,by simp⟩ (fun a b _ _ h q=>?_) (fun t a _ h=>?_) (jury P H)
 · rintro _ ⟨i,rfl⟩;exact ⟨|W i|,abs_nonneg _,fun B _ hp hs=>(hs i).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)⟩
 · obtain ⟨C,hC,H⟩:=h;obtain ⟨D,hD,G⟩:=q;refine ⟨C+D,add_nonneg hC hD,fun B x hp hu=>?_⟩;rw [LinearMap.add_apply,add_mul];exact (abs_add_le ..).trans (add_le_add (H B x hp hu) (G B x hp hu))
 obtain ⟨C,hC,H⟩:=h;refine ⟨|t| * C,mul_nonneg (abs_nonneg _) hC,fun B x hp hu=>?_⟩; rw [LinearMap.smul_apply,smul_eq_mul,abs_mul,mul_assoc];exact mul_le_mul_of_nonneg_left (H _ _ hp hu) (abs_nonneg _)
variable {A:Type}[NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A]{L:U→ₗ[ℝ]A}
/-- Price moving tensor application over all directions simultaneously. -/
lemma jury_prize (H:∀ v:U,(∀ t,P t v=0)→L v=0)(W:I→ℝ):∃ C:ℝ,0≤C∧∀(B:ℝ)(x:U),0≤B→(∀t,|P t x|≤W t*B)→‖L x‖≤C*B:=by
 let Yb:=Module.finBasis ℝ A
 let G'(i):=(Yb.coord i).comp L
 choose D hD G using fun i=> court P (g:=G' i) (fun v h=>show Yb.coord i (L v)=0 by rw [H v h,map_zero]) W
 refine ⟨∑ i,D i*‖Yb i‖,Finset.sum_nonneg (fun _ _=>mul_nonneg (hD _) (norm_nonneg _)),fun B x hp hh=>?_⟩
 rw [←Yb.sum_repr (L x),sum_mul]; apply (norm_sum_le ..).trans (sum_le_sum fun i _=>?_);rw [norm_smul];change |G' i x| * ‖Yb i‖ ≤ _;exact (mul_le_mul_of_nonneg_right (G i B x hp hh) (norm_nonneg _)).trans_eq (by ring)
-- Calibration subspace. Only one h at a time, m read-qualified at that grade only.
def fawn (G:Gauge)(d p:ℕ):Submodule ℝ (Harp G d p) where
 carrier:={M|Tensor.Sym M}
 zero_mem':=fun _ _=>rfl
 add_mem':=fun (a : Tensor.Sym _) (b:Tensor.Sym _) v t=>congrArg₂ (·+·) (a v t) (b v t)
 smul_mem':=fun c _ (a : Tensor.Sym _) v t=>congrArg (c • ·) (a v t)
lemma f_actual (i:↥(fawn G d p)):Tensor.Sym i.val:=i.property

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000
lemma disc (M:Module.Dual ℝ (Harp G d p))(h:Y→ℝ) :∃ C:ℝ,0≤C∧ ∀ x:Harp G d p,∀ B:ℝ,0≤B→Tensor.Sym x→(∀ v:Y,|Tensor.diagonal x v|≤h v*B)→ |M x|≤C*B:=by
 let U:=↥(fawn G d p);let F(v:Y):=(pointT (fun _:Fin p=>v)).comp (fawn G d p).subtype
 have vfix (v:U) (hv:∀ i,F i v=0):(M.comp ((fawn G d p).subtype)) v=0:=by
    change M v.val=0;rw [Tensor.ext_diag v.val 0 (f_actual v) (fun _ _=>rfl) (funext (fun i=> hv i)),map_zero]
 obtain ⟨C,hC,H⟩:= court F vfix h
 exact ⟨C,hC,fun x B hp hu ht=> H B (⟨x,hu⟩:U) hp ht⟩
-- graded variables.
def memorial (X:Labels.Frame G d)(p k:ℕ):Harp G d p→ₗ[ℝ] Pol G:=∑ i:X.Index,LinearMap.smulRight (tally X p k i) (X.basis i).val
def Validity (X:Labels.Frame G d)(p k:ℕ):Submodule ℝ (Harp G d p):=fawn G d p ⊓ LinearMap.ker (canvas G d p k - memorial X p k)
lemma admitted (X:Labels.Frame G d)(x:Harp G d p) : x∈Validity X p k ↔ Tensor.Sym x ∧ canvas G d p k x = ∑ i, tally X p k i x • (X.basis i).val:=by
 change (_∧ _=0) ↔ _;rw [LinearMap.sub_apply,sub_eq_zero,memorial,LinearMap.sum_apply];simp_rw [LinearMap.smulRight_apply]; rfl
lemma admission (X:Labels.Frame G d)(x:Harp G d p)(h:Tensor.Sym x){Q:Label G d}(he:Q.val=tile (paintBand x) k):x∈Validity X p k:= (admitted X x).mpr ⟨h,by
 rw [canvasTile,←he];simp_rw [← IsScalarTower.algebraMap_smul ℂ (tally X p k _ _)] -- pattern placeholders
 change Q.val=∑ i:X.Index,(tally X p k i x:ℂ) • _;simp_rw [tally_label X x he]
 change (localFields G d).subtype Q= ∑ i:X.Index,X.basis.repr Q i • (localFields G d).subtype (X.basis i);simp_rw [←_root_.map_smul];rw [←map_sum,X.basis.sum_repr]⟩
private lemma det (X:Labels.Frame G d)(x:↥(Validity X p k))(hs:∀ i:X.Index,(X.grades i)=(k,p)→ tally X p k i x.val=0)(he:(memorial X p k) x.val =∑ i:X.Index with (X.grades i)=(k,p),tally X p k i x.val • (X.basis i).val):tile (paintBand x.val) k=0:=by
 rw [← canvasTile, ((admitted X x.val).mp x.property).2]
 unfold memorial at he
 rw [LinearMap.sum_apply] at he
 simp_rw [LinearMap.smulRight_apply] at he
 rw [he]
 exact sum_eq_zero fun i hi => by rw [hs i (mem_filter.mp hi).2, zero_smul]

abbrev factors {p:ℕ}(b:Fin p→ Fin (d-1)):= ContinuousMultilinearMap ℝ (fun i=>Taylor G (b i).val) ℝ
-- FD instance directly
instance f_fd (b:Fin p→Fin (d-1)):FiniteDimensional ℝ (@factors G d p b):=by
 letI (i : Fin p) : Module.Finite ℝ (Taylor G (b i).val) := inferInstance
 letI (i : Fin p) : Module.Free ℝ (Taylor G (b i).val) := inferInstance
 letI : Module.Finite ℝ (MultilinearMap ℝ (fun i : Fin p => Taylor G (b i).val) ℝ) :=
   Module.Finite.multilinearMap (R := ℝ) (M₁ := fun i : Fin p => Taylor G (b i).val) (M₂ := ℝ)
 exact FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
   ContinuousMultilinearMap.toMultilinearMap_injective

def per (G:Gauge){d p:ℕ}(b:Fin p→Fin (d-1)):Harp G d p→ₗ[ℝ] factors (G:=G) b where
 toFun M:=M.compContinuousLinearMap fun i=> ContinuousLinearMap.single ℝ (fun j:Fin (d-1)=>Taylor G j.val) (b i)
 map_add' _ _:=by ext;rfl
 map_smul' _ _:=by ext;rfl
/-- Cost of any pure list read by basis tallies. Caller supplies bounds for ALL indices,
 off-grade tallies vanish on admitted packets since through d & pure, not presumed here. -/
lemma coinage (X:Labels.Frame G d)(b:Fin p→Fin (d-1)):
 ∃ C:ℝ,0≤C∧∀ M:Harp G d p,∀ B:ℝ,M∈Validity X p (rate b)→0≤B→(∀ i:X.Index,|tally X p (rate b) i M|≤B)→‖per G b M‖≤C*B:=by
 let V:=Validity X p (rate b);let Q:=fun i=> (tally X p (rate b) i).comp V.subtype;let F:↥V→ₗ[ℝ]_:= (per G b).comp V.subtype
 have vfix (u:↥V) (hu:∀ i,Q i u=0):F u=0:=by
   ext1 x
   let N:=u.val
   obtain ⟨hs,hW⟩:=(admitted X N).mp u.property
   have hh : tile (paintBand N) (rate b)=0:=by rw [←canvasTile,hW];apply sum_eq_zero;intro i _; rw [show tally X _ _ i N=0 from hu i,zero_smul]
   exact Complex.ofReal_injective (show (paintBand N (fun i=>Pi.single (b i) (x i)))=(↑(0:ℝ):ℂ) by rw [tile_detects (paintBand N) (fun v w=>congrArg (fun y:ℝ=>(↑y:ℂ)) (hs v w)) b hh x];simp)
 obtain ⟨C,hC,H⟩:=jury_prize Q (A:=factors (G:=G) b) vfix (fun _=>1)
 refine ⟨C,hC,fun M B hp hB ht=>H B (⟨M,hp⟩:↥V) hB (fun i=>?_ )⟩
 rw [one_mul];exact ht i
end YM.RG08.Trill
