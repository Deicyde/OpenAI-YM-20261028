import YM.RG08.Yurt.Cairns

/-! # Band with joint ratio scale at polynomial order, after displacement. Can recover all
lower weight coefficients with same pre cost; no matrix norms tacitly L-dependent. Includes
scalar tensors and site profiles, ν intended separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt
open scoped Classical ContDiff BigOperators Topology
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {n m:ℕ}{u D C:ℝ}

abbrev Dust (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ):=(i:Fin n)→Tensor.T E4 E i.val
def still (q:Dust E n):Prop:=∀ i:Fin n,Tensor.Sym (q i)
def mix (q:Dust E n):E4→E :=∑ i,Tensor.diagonal (q i)
lemma mix_smul (q:Dust E n)(a:ℝ):mix (a • q)=a • mix q:=by unfold mix;rw [smul_sum];apply sum_congr rfl;intro i _;rfl
lemma reading(f:E4→E)(h:f∈ rangeLt E n):∃ q:Dust E n,still q ∧ mix q=f:=by
 obtain ⟨v,hv,rfl⟩:=range_decompose h; choose T hT he using (fun i=>pure_sym (hv i))
 exact ⟨T,hT,sum_congr rfl (fun i _=> (he i).symm)⟩
lemma mixing(q:Dust E n):mix q∈Place.rangeLt E n:= Submodule.sum_mem _ (fun i _=>exact_le_band i.isLt (Place.simple _))
lemma hit (q:Dust E n)(x:E4)(w:ℝ): mix q (w • x)= ∑ i,w^i.val • Tensor.diagonal (q i) x:=by
 unfold mix;rw [Finset.sum_apply];apply sum_congr rfl;intro i _;exact Tensor.homogeneous ..
lemma hear [FiniteDimensional ℝ E] {x:Fin n→E}(he:∀ a:ℝ,∑ i:Fin n,a^i.val • x i=0):x=0:=by
 cases n with
 | zero=>funext i;exact i.elim0
 | succ n=>
    funext i
    by_contra H
    obtain ⟨R,hR⟩:= Module.Projective.exists_dual_ne_zero ℝ H
    have hp:=Flint.sounds (R:=n) (p:=fun i=>R (x i)) (fun a=>by simpa using congrArg R (he a))
    exact hR (congrFun hp i)
lemma dust_clear [FiniteDimensional ℝ E](q:Dust E n)(he:still q)(h:mix q=0):q=0:=by
 funext i
 apply Tensor.ext_diag (q i) 0 (he i) (fun _ _=>rfl);funext x
 have ht:=hear (x:=fun i:Fin n=>Tensor.diagonal (q i) x) (fun a=>by rw [←hit,h];rfl)
 exact congrFun ht i

def Board (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ):Submodule ℝ (Dust E n) where
 carrier:={q|still q}
 zero_mem':=fun _ _ _=>rfl
 add_mem':=fun hx hy i v p=>congrArg₂ (·+·) (hx i v p) (hy i v p)
 smul_mem':=fun c _ hx i v p=>congrArg (c • ·) (hx i v p)
abbrev crew (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ):=↥(Board E n)
def preview (x:E4):Dust E n→ₗ[ℝ] E where
 toFun q:=mix q x
 map_add' _ _:=by unfold mix;rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,←sum_add_distrib]; apply sum_congr rfl; intro i _;rfl
 map_smul' a v:=by rw [mix_smul];rfl

variable [FiniteDimensional ℝ E]
open Set in
-- compact sensor with bound K uniform. Works n even at one-dimension E triv.
theorem industry (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](n:ℕ):∃ W:ℝ,1≤W ∧ ∀ (q:Dust E n),still q→∀ K:ℝ,0≤K → (∀ x:E4,‖mix q x‖≤ K*(1+‖x‖)^n)→‖q‖≤W*K:=by
 let t(x:E4):= (preview x: Dust E n→ₗ[ℝ] E)
 let S:= Metric.sphere (0:crew E n) 1
 let U(p:E4×ℝ):= {z:crew E n| ‖z‖<p.2*‖t p.1 z.val‖}
 have hc(i):Continuous (t i):= LinearMap.continuous_of_finiteDimensional _
 have hg:S⊆ ⋃ p,U p:=by
    intro z hz;apply mem_iUnion.mpr
    change dist z 0=1 at hz; rw [dist_zero_right] at hz
    have ht:∃ x,0<‖t x z.val‖:=by
       by_contra! he
       have ht:z=0:=Subtype.ext (dust_clear _ z.property (funext fun x=> norm_le_zero_iff.mp (he x)))
       rw [ht,norm_zero] at hz; exact zero_ne_one hz
    obtain ⟨x,hx⟩:=ht
    refine ⟨(x,(‖z‖+1)/‖t x z.val‖),?_⟩;change ‖z‖< (‖z‖+1)/_*_;rw [div_mul_cancel₀ _ hx.ne']; simp
 letI : ProperSpace (crew E n):=FiniteDimensional.proper ℝ _
 obtain ⟨l,hL⟩:=(isCompact_sphere (0:crew E n) 1).elim_finite_subcover U (fun p=>isOpen_lt continuous_norm (continuous_const.mul (((hc _).comp continuous_subtype_val).norm))) hg
 let C (p:E4×ℝ):=|p.2| *(1+‖p.1‖)^n;have hC(p):0≤C p:=by unfold C; positivity
 refine ⟨1+∑ i∈l,C i,le_add_of_nonneg_right (sum_nonneg fun i _=>hC i),fun q hq K hK hh=>?_⟩
 by_cases h:q=0
 · rw [h,norm_zero];exact mul_nonneg (add_nonneg zero_le_one (sum_nonneg (fun i _=>hC i))) hK
 have hp:=norm_pos_iff.mpr h
 let z:crew E n:=⟨q,hq⟩; let a:=‖q‖⁻¹
 have ha:a • z ∈ S:=by simp [S,norm_smul,h,z,a]
 obtain ⟨i,hi,h⟩:=mem_iUnion₂.mp (hL ha)
 have hs:‖a‖*‖q‖<‖a‖*(i.2*‖mix q i.1‖):=by
    change ‖a • q‖ < i.2*‖t i.1 (a • q)‖ at h;rw [_root_.map_smul,norm_smul,norm_smul,mul_left_comm] at h;exact h
 have hb:=lt_of_mul_lt_mul_left hs (norm_nonneg _)
 apply hb.le.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans ?_)
 apply (mul_le_mul_of_nonneg_left (hh i.1) (abs_nonneg _)).trans
 exact (show |i.2| *(K*(1+‖i.1‖)^n)=C i*K from by unfold C;ring).trans_le (mul_le_mul_of_nonneg_right ((single_le_sum (f:=C) (fun i _=>hC i) hi).trans (le_add_of_nonneg_left zero_le_one)) hK)

-- Lead scale ε with engineering σ per field (=ε, No. letters), homogeneous i gains ε^i.
structure Pool (u:ℝ)(n m:ℕ)(x:E4→E)(D:ℝ):Prop where
 band : x∈Place.rangeLt E n
 nice : 0≤D
 shape : ∀ y:E4,‖x y‖≤D*u^m*(1+u*‖y‖)^n

-- INPUT pool -> packet cost, pays BEFORE L and EAR after restrictions. Has weight for pal or field/marks. m≥0
lemma disclose (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](n:ℕ):∃ C:ℝ,1≤C ∧∀(q:Dust E n){u D:ℝ}{m:ℕ},still q → Pool u n m (mix q) D → 0<u → ∀ i:Fin n,‖q i‖≤ C*D*u^(m+i.val):=by
 obtain ⟨C,hC,H⟩:=industry E n
 refine ⟨C,hC,fun q u D m hq hw h i=>?_⟩
 let z:Dust E n:=fun i=>u⁻¹ ^ (i.val+m) • q i
 have hz:still z:=fun b x p=>congrArg (u⁻¹^(b.val+m) • ·) (hq b x p)
 have hh(x:E4): mix z x=u⁻¹^m • mix q (u⁻¹ • x):=by
    rw [hit, mix, Finset.sum_apply,smul_sum];apply sum_congr rfl;intro i _
    unfold z;rw [smul_smul,mul_comm,pow_add];rfl
 have ha: 0≤u⁻¹:=by positivity
 have he(x:E4):‖mix z x‖ ≤D*(1+‖x‖)^n:=by
    rw [hh,norm_smul,Real.norm_of_nonneg (pow_nonneg ha _)]
    apply (mul_le_mul_of_nonneg_left (hw.shape (u⁻¹ • x)) (pow_nonneg ha m)).trans_eq
    rw [norm_smul,Real.norm_of_nonneg ha,←mul_assoc u,mul_inv_cancel₀ h.ne',one_mul]
    rw [inv_pow]; field_simp
 have ht:‖z i‖ ≤ C*D:= (norm_le_pi_norm z i).trans (H z hz D hw.nice he)
 unfold z at ht;rw [norm_smul,Real.norm_of_nonneg (pow_nonneg ha _),inv_pow,mul_comm, ←div_eq_mul_inv,Nat.add_comm,div_le_iff₀ (pow_pos h _)] at ht;exact ht

omit [FiniteDimensional ℝ E] in
lemma Pool.up {x:E4→E}(hu:0≤u)(hh:Pool u n m x D)(hd:D≤C){p:ℕ}(hp:n≤p):Pool u p m x C:=by
 refine ⟨Place.grows E hp hh.band,hh.nice.trans hd,fun i=>(hh.shape i).trans ?_⟩
 exact mul_le_mul (mul_le_mul_of_nonneg_right hd (pow_nonneg hu _)) (pow_le_pow_right₀ (le_add_of_nonneg_right (mul_nonneg hu (norm_nonneg _))) hp) (by positivity) (mul_nonneg (hh.nice.trans hd) (pow_nonneg hu _))

/- Shift at root by h v for bounded $u\|v\|$. no deterioration of weights for weakened
 coefficients, verified in joint filtration. -/
omit [FiniteDimensional ℝ E] in
lemma Pool.turn {x:E4→E}(hu:0≤u)(h:Pool u n m x D){v:E4}{B:ℝ}(hb:u*‖v‖≤B):Pool u n m (fun w=>x (w+v)) (D*(1+B)^n) ∧ (fun w=>x (w+v)-x w) ∈ Place.rangeLt E (n-1):=by
 have hf:0≤B:=(mul_nonneg hu (norm_nonneg _)).trans hb
 refine ⟨⟨band_shift h.band v,mul_nonneg h.nice (by positivity),fun y=>(h.shape _).trans ?_⟩,band_step (n:=n-1) (Place.grows E (by cases n<;>simp) h.band) v⟩
 have hx : 1+u*‖y+v‖ ≤ (1+B)*(1+u*‖y‖):=by
    nlinarith only [mul_le_mul_of_nonneg_left (norm_add_le y v) hu,hf,hb,mul_nonneg hf (mul_nonneg hu (norm_nonneg y))]
 exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx n) (mul_nonneg h.nice (pow_nonneg hu m))).trans_eq (by rw [mul_pow];ring)
end YM.RG08.Halo
