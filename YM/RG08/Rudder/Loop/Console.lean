import YM.RG08.Rudder.Sym.Lien

noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical ENNReal InnerProductSpace
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain Symmetry Filter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {I:Type} {G:Gauge}{σ C B:ℝ}{F T:Raw I 2}

lemma spectrum_pays {a b:Tablet}(hc:0≤C)(hs:0≤σ)(h:Held (carpet (Tone I)) σ C F)(y:Tape 2 I) :
 RG.SumBudget (fun v : Cover=> |col (hum F y) a b v|) C:=by
 let t(v:Cover):=lyre (place (0,a) (v,b)) y
 have hf:Function.Injective t:=by intro v w he;exact congr_arg (fun x:Tape 2 (Market (Tone I))=> (x p).1) he
 have hh:∑' w:Cover, ENNReal.ofReal |F (t w)| ≤ ENNReal.ofReal C:=by
   apply le_trans (b:=∑' w:Cover,Forms.row (mark (carpet (Tone I)) σ F) o (0,a,y o) (t w))
   · apply ENNReal.tsum_le_tsum; intro w;rw [Forms.row,if_pos (show t w o=(0,a,y o) from rfl)];apply ENNReal.ofReal_le_ofReal;exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hs (Ground.radius_nn ..)))
   exact (ENNReal.tsum_comp_le_tsum_of_injective hf _).trans (ensign.mp h o _)
 let f(v:Cover):= |F (t v)|
 have hr:∑'v,ENNReal.ofReal (f v)≠⊤:=ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh
 have he:Summable f:= (ENNReal.summable_toReal hr).congr (fun x=>ENNReal.toReal_ofReal (abs_nonneg _))
 change ∑' v,ENNReal.ofReal (f v)≤_ at hh
 rw [←ENNReal.ofReal_tsum_of_nonneg (f:=f) (fun _=> abs_nonneg _) he] at hh
 exact ⟨fun _=>abs_nonneg _,he,(ENNReal.ofReal_le_ofReal_iff hc).mp hh⟩

lemma spectrum_pence {a b:Tablet}(hc:0≤C)(hs:0≤σ)(h:Held (carpet (Tone I)) σ C F)(y:Tape 2 I):|spectrum F a b y|≤C:=by
 have he:=spectrum_pays (a:=a) (b:=b) hc hs h y
 have hu:=norm_tsum_le_tsum_norm (f:=col (hum F y) a b) (by simpa only [Real.norm_eq_abs] using he.2.1)
 simpa only [Real.norm_eq_abs,spectrum,load] using hu.trans (show _≤C by simpa only [Real.norm_eq_abs] using he.2.2)

lemma spectrum_minus (a b:Tablet)(hc:0≤C)(ht:0≤B)(hs:0≤σ)(h:Held (carpet (Tone I)) σ C F)(H:Held (carpet (Tone I)) σ B T)(y:Tape 2 I): spectrum (F-T) a b y = spectrum F a b y - spectrum T a b y:=by
 have he{F:Raw I 2}{M:ℝ}(hc:0≤M)(h:Held (carpet (Tone I)) σ M F):Summable (col (hum F y) a b):=Summable.of_norm (by simpa only [Real.norm_eq_abs] using (spectrum_pays (a:=a) (b:=b) hc hs h y).2.1)
 exact (he hc h).tsum_sub (he ht H)

lemma spectrum_hue [Fintype I]{V:Submodule ℝ (Urn I 2)}(hf:hue V F)(hs:0≤σ)(hc:0≤C)(h:Held (carpet (Tone I)) σ C F)(a b:Tablet):spectrum F a b∈ V:=by
 have he:HasSum (fun v:Cover=>(hat F (place (0,a) (v,b)):Urn I 2)) (spectrum F a b):= by rw [HasSum,tendsto_pi_nhds];intro i;simp_rw [Finset.sum_apply]; exact (show Summable (col (hum F i) a b) from Summable.of_norm (by simpa only [Real.norm_eq_abs] using (spectrum_pays (a:=a) (b:=b) hc hs h i).2.1)).hasSum
 exact Submodule.closed_of_finiteDimensional V |>.mem_of_tendsto he (Eventually.of_forall fun i=> sum_mem fun v _=>hf _)

/- Bilinear color pairing at shape. -/
private def bar (f:Urn G.ColorIndex 2): G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ := ∑ y, f y • ((EuclideanSpace.projₗ (y o):G.Color→ₗ[ℝ] ℝ).smulRight (EuclideanSpace.projₗ (y p)))
def both (x y:G.Color):Tape 2 G.Color:=Fin.cons x (fun _=>y)
lemma both_pair(f:Urn G.ColorIndex 2)(x:Tape 2 G.Color):bar f (x o) (x p)=sing f x:=by
 unfold bar sing; simp only [Fin.prod_univ_succ,prod_of_isEmpty,mul_one,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.smulRight_apply,smul_eq_mul];rfl -- maybe duplicate sum_apply ok
private lemma ad_rule(f:Urn G.ColorIndex 2)(h:f∈dressed G 2)(x y z:G.Color):bar f (G.ad x y) z= -bar f y (G.ad x z):=by
 have he:(∑ i,sing f (update (both y z) i (G.ad x (both y z i))))=0:= (show _ ∧ _ from h).2 x (both y z)
 simp only [Fin.sum_univ_succ,sum_of_isEmpty,add_zero,← both_pair,update_self,update_of_ne (Fin.succ_ne_zero _),update_of_ne (Ne.symm (Fin.succ_ne_zero _))] at he -- ?
 exact eq_neg_of_add_eq_zero_left he

private lemma crossed_ (f:Urn G.ColorIndex 2)(h:∀ y,f y=f (y ∘ Equiv.swap o p))(x y:G.Color):bar f x y=bar f y x:=by
 have he:=sing_perm f (Equiv.swap o p) (both x y)
 rw [←funext h,←both_pair,←both_pair] at he
 simpa [both] using he

lemma stereo {F:Raw G.ColorIndex 2}(h:Cloak (dressed G 2) 2 F)(hΓ: G.Simple)(hp:Held (carpet (Tone G.ColorIndex)) σ C F)(hs:0≤σ)(hc:0≤C)(a:Tablet)(ha:a.card=2) :
 ∃ β:ℝ,∀ b c:Tablet,b.card=2→c.card=2→∀ y:Tape 2 G.ColorIndex,spectrum F b c y = if b=c∧y o=y p then β else 0:=by
 let f:=spectrum F a a
 have h1:f∈dressed G 2:=spectrum_hue h.hair hs hc hp _ _
 obtain ⟨β,hβ⟩:=Gauge.invariant_scalar hΓ (bar f) (crossed_ f (fun y=>spectrum_sym h.path h.beam ..)) (ad_rule f h1)
 have he(y): f y = if y o=y p then β else 0:=by
    rw [←pin_single f y,←both_pair,hβ]; simp only [comp_apply, orthonormal_iff_ite.mp (EuclideanSpace.basisFun G.ColorIndex ℝ).orthonormal,mul_ite,mul_one,mul_zero]
 refine ⟨β,fun b c hb hc y=>?_⟩
 rcases eq_or_ne b c with rfl|hh
 · rw [←spectrum_on h.path h.firm a b (by omega) y];change f y=_;simp only [he, eq_self,true_and]
 rw [spectrum_off h.path h.firm h.field' b c hh _];simp [hh] -- remove
end YM.RG08.Rudder.Loop
