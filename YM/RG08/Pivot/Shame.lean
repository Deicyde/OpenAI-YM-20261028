import YM.RG08.Pivot.Whim

/-! # Each symbol layer preserves the colors and transversality
before phase transforms. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Drift
open UVExt.Paths Scores Loom Shade Quire Tall Vale Planned.PrimaryIntegral295 Analysis Reflect
open scoped Topology BigOperators Classical InnerProductSpace
variable {G:Gauge} {c f L: Side} {T: Ratio c f}{d r n D : ℕ} {R k : ℝ}
def stainM (c:Side) (p:G.El): Matrix (Lines G c 1) (Lines G c 1) ℝ:= LinearMap.toMatrix' (stain (G:=G) (m:=c) p).toLinearMap
lemma stain_leg (c : Side)(p:G.El)(x:Link G c): stainM c p *ᵥ x=stain p x := LinearMap.toMatrix'_mulVec ..
lemma arm_silver (c : Side)(p:G.El)(x:Link G c)(z:Body 1 c): arm G c 1 (stain p x) z=G.adjoint p (arm G c 1 x z):= by
    unfold stain; rw [ContinuousLinearMap.comp_apply]; simp only [ContinuousLinearEquiv.coe_coe,(arm _ _ _).apply_symm_apply]; rfl
lemma stains_preserved (p : G.El)(P: Matrix (Body 1 c) (Body 1 c) ℝ) :
    stainM c p * tensor G P * (stainM c p)ᵀ=tensor G P := by
  let s:= stainM c p
  let h: G.Color→ₗᵢ[ℝ] G.Color:= ⟨G.adjoint p,G.norm_adjoint p⟩
  have he (x y:Link G c) : dotProduct x y = ∑ i:Body 1 c, inner ℝ (arm G c 1 x i) (arm G c 1 y i) := by
    rw [component_dot]; unfold dotProduct; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; exact color_dot (G:=G) (arm G c 1 x i) (arm G c 1 y i)
  have ht: Military s:= military_intro _ (fun i j=> by simp_rw [s,he,stain_leg,arm_silver]; exact Finset.sum_congr rfl fun i _=> LinearIsometry.inner_map_map h _ _)
  have hh: s*tensor G P=tensor G P*s := by
    apply matrix_eq; intro x; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,show s *ᵥ x= _ from stain_leg c p x]
    have he (x:Link G c)(i:Body 1 c) : arm G c 1 (tensor G P *ᵥ x) i=∑ j:Body 1 c,P i j • arm G c 1 x j:= by ext1 j; rw [WithLp.ofLp_sum, Finset.sum_apply]; exact congr_fun (component_mul P x j) i
    apply (arm G c 1).injective; funext z; rw [show s*ᵥ _= _ from stain_leg c p _,arm_silver]; simp_rw [he, arm_silver,map_sum,_root_.map_smul]
  rw [show stainM c p*tensor G P=_ from hh,Matrix.mul_assoc, show s*(stainM c p)ᵀ=1 from ht.left, Matrix.mul_one]
variable {W: Spine (Voice D R) (Loc G 1)}
lemma all_colours (hp: Gold (W r)) {m:Side}(o:Site m)(φ:Exam D)(k:G.El) : twistV (stainM m k) (recitalP (W r) o φ) = recitalP (W r) o φ:= by
  let p:=stainM m k
  let K:=recitalP (W r) o φ
  have he : Tensor.Sym K:= (Tidy.map _ hp.toTidy).sym _
  apply Tensor.ext_diag _ _ (turns_sym _ he) he
  have hx : Tensor.diagonal (twistV p K)=ᶠ[𝓝 0] Tensor.diagonal K := by
    filter_upwards [hp.seatM m φ o k] with x hv
    unfold Tensor.diagonal; change twistV p K _= _; rw [twists]; simp_rw [p,stain_leg]; exact hv
  have hh := Tensor.GermCoeff r hx
  rw [coeff_at_diagonal _ (turns_sym p he), coeff_at_diagonal K he] at hh; exact congr_arg _ hh
variable {v : Train n}
-- only on shared actual periods, then assemble
lemma fig_march (hs : 0<k)(hn:4 ≤ n) (m:Side)(hm: Even m.val)(w : Train n) (hp:∀ i,Gold (W i))(o:Site m)(φ:Exam D)(i:G.El):
    let F:= recitalP (fig (plaza G k w (some m)) W d r) o φ
    twistV (stainM m i) F=F:= by
  obtain ⟨C,hC,H⟩:=portion G hs hn
  let X:=fun r=> recitalP (W r) o φ
  let P:=tensor G (bedtime k w m)
  intro F
  have ht: F=terraces P X d r:= fig_earned P o ((H w).2 _ hm) (fun _ _=> plaza_m ..) (fun i=> (hp i).toTidy) (plug φ R) d r
  have he := terraces_swap P (stainM m i) X d r; have hv:= stains_preserved i (bedtime k w m)
  rw [show _*P*(stainM m i)ᵀ=P from hv,show (fun r=> _) = X from funext fun r=> all_colours (hp r) o φ i] at he; rw [ht]; exact he.symm
lemma fig_sober_finite (hs:0<k)(hn:4 ≤ n)(m:Side)(hm:Even m.val)(w : Train n)(h:∀ i,Gold (W i))(o:Site m)(φ:Exam D)(a:Fin r)(v:Fin r→Link G m)(P:Vec G m 0)(hx:v a=gradient P):
    recitalP (fig (plaza G k w (some m)) W d r) o φ v=0:= by
  obtain ⟨C,hC,H⟩:=portion G hs hn
  let f i:= recitalP (W i) o φ
  let M:=tensor G (bedtime k w m)
  rw [show recitalP (fig (plaza G k w (some m)) W d r) o φ=_ from fig_earned M o ((H w).2 _ hm) (fun _ _=> plaza_m o _) (fun i=> (h i).toTidy) (plug φ R) d r]
  change terraces M f d r v=0
  induction d generalizing r with
  | zero=> rw [terraces]; exact (h r).lucid _ _ _ _ _ _ hx
  | succ i IH=>
    rw [terraces,_root_.smul_apply,bur_eval,Finset.sum_eq_zero (fun i _=>?_)]
    · simp
    refine Finset.sum_eq_zero fun b _=> ?_; rw [IH (a:=a.succ.succ),mul_zero]; simpa only [Fin.cons_succ] using hx

-- exact tiling preserves gradients
lemma tonal (T: Ratio c f)(G:Gauge) (p:Vec G T.count 0) : tiltCopy T G (gradient p)=gradient (fun i: Slot G f 0=>p (T.residue i.1,i.2)) := by
  funext i; rcases i with ⟨i,a,j⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective a; rw [coord_map]; change gradient p (T.residue i,coord a,j)=_; rw [grad_corner,grad_corner]; dsimp only; rw [map_add,tilt_step]
lemma tone_wash (T:Ratio c f)(s:G.El)(v:Link G T.count) : stain s (tiltCopy T G v) = tiltCopy T G (stain s v) := by
    have h (P: Link G T.count)(i:Site f)(j): arm G f 1 (tiltCopy T G P) (i,j)=arm G T.count 1 P (T.residue i,j) := rfl
    apply (arm G f 1).injective; funext i; rcases i with ⟨x,i⟩; rw [arm_silver,h,h,arm_silver]
lemma rec_copy (T:Ratio c f) {U:EnvelopeU D R G r}(h:Pens U)(φ:Exam D)(o:Site f)(v:Fin r→Link G T.count):
    recitalP U o φ (tiltCopy T G ∘ v)=recitalP U (T.residue o) φ v:= by
  unfold recitalP; simp_rw [stitch_apply (h.shaped (plug φ R)).of_norm]; refine tsum_congr fun i=> ?_
  congr 1; unfold rosary; apply Finset.prod_congr rfl; intro k _
  unfold silks; change v k (T.residue (o+wrap f _),_)=v k _; rw [map_add,T.residue_wrap]
-- preserves Gold at all roots on all sides
lemma golden_terraces (hs:0<k)(hn:4 ≤ n)(h:∀ i,Gold (W i)) (v : Train n) (r d : ℕ): Gold (fig (plaza G k v none) W d r) := by
    let f:=fig (plaza G k v none) W d r
    obtain ⟨C,hC,H⟩:=portion G hs hn
    refine ⟨⟨song_front (H v).1 (fun i=> (h i).toTidy) d r,?_⟩,?_⟩
    all_goals
      intro m
      let c(i):=even_side i*m
      have ht: Tendsto (fun i=> (c i).val) atTop atTop:= tendsto_atTop_mono (fun i=> Nat.le_mul_of_pos_right (even_side i).val m.property) evenings_grow
      have hv i: Even (c i).val:= (evenings i).mul_right _
      let U i:= fig (plaza G k v (some (c i))) W d r
      have hu : Hurled U f := fare_front (H v).1 (P:=fun i=> plaza G k v (some (c i))) (dormer G hs hn v c ht hv) (fun i=>(H v).2 _ (hv i)) (fun i=> Hurled.fixed (h i).pens) d r
      have hh (o:Site m)(φ:Exam D)(y: Fin r→Link G m): Tendsto (fun i=> recitalP (U i) o φ y) atTop (𝓝 (recitalP f o φ y)):= (ContinuousMultilinearMap.apply ℝ (fun _:Fin r=>Link G m) ℝ y).continuous.continuousAt.tendsto.comp (pens_tuft (hu.maps (plug φ R)) m o)
      let T (i:ℕ):Ratio (even_side i) (c i):=⟨m,rfl⟩
    · intro φ o s; refine Eventually.of_forall fun x:Link G m=>?_
      apply tendsto_nhds_unique_of_eventuallyEq (hh o φ (fun _=>stain s x)) (hh o φ (fun _=> x)) (Eventually.of_forall fun i=> ?_)
      let p:=T i; let k:= p.assemble (0,o)
      have hp : p.residue k=o:=p.assemble_res (0,o)
      calc
        _ = recitalP (U i) k φ (fun _=> tiltCopy p G (stain s x)) := by rw [show (fun _ : Fin r=> tiltCopy p G (stain s x))=(tiltCopy p G ∘ fun _=>stain s x) from rfl,rec_copy p (hu.ever i),hp]
        _ = recitalP (U i) k φ (fun _=> tiltCopy p G x) := by
          have hX:= DFunLike.congr_fun (fig_march (d:=d) (r:=r) hs hn _ (hv i) v h k φ s) (fun _=>tiltCopy p G x)
          rw [twists] at hX; simp_rw [stain_leg, tone_wash] at hX; exact hX
        _=_ := by rw [show (fun _ : Fin r=> tiltCopy p G x)=(tiltCopy p G ∘ fun _=>x) from rfl, rec_copy p (hu.ever i),hp]
    intro o φ a v' g hg
    exact tendsto_nhds_unique_of_eventuallyEq (hh o φ v') tendsto_const_nhds (Eventually.of_forall fun i=>by
      let p:= T i; let k:= (T i).assemble (0,o)
      have he : tiltCopy p G (v' a)= _:= (congr_arg (tiltCopy p G) hg).trans (tonal p G _)
      change recitalP (U i) o φ v'=0
      calc _=recitalP (U i) k φ (tiltCopy p G ∘ v'):= by rw [rec_copy p (hu.ever i), show p.residue k=o from p.assemble_res _]
           _=_:= fig_sober_finite hs hn _ (hv i) v h _ φ a _ _ he)
end YM.RG08.Pivot
