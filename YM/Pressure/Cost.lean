import YM.Branch.Predict
import YM.Pressure.Gauge
import YM.Pressure.Macro

/-!
# Qchd truly actual prediction. Produce on universal L old/new inputs.

Macro stencil counts covered copies, may have repetitions on short tori.
Transfer/cancellation uses it WITH volume receipt. For local tickets
accept also weaker support on site outcomes at incident anchors, no assumption
on likelihood away. Density only requests tags with positive probability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Filter Function Lattice RG RG.Patch Axial Wilson Finset YM.Branch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal
variable {G : Gauge}

private lemma carries (j : ℕ) (P : Patch) (h : j=P.J) (s : ℕ) :
    (2*(P.radius+s*P.L.val)+1:ℝ) ≤ (2*(j+3+s:ℕ)+1:ℝ)* P.L.val := by
  have hw : (1:ℝ)≤P.L.val := by exact_mod_cast Nat.succ_le_iff.mpr P.L.property
  unfold radius; push_cast; rw [h]; linarith

variable {c f : Side} (S : StepData c f)

abbrev plank (x : Site c) (y : Cover) : Site c := wrap c y + x
def centerRoot (P : Patch) (y : Cover) := P.L.val • y

lemma offsets (x : Site c) (y : Cover) : S.ratio.embed (plank x y)=wrap f (centerRoot S.patch y)+S.ratio.embed x := by
  rw [plank, show S.ratio.embed _ = S.ratio.embed (wrap c y)+S.ratio.embed x from S.ratio.root.map_add _ _, Ratio.embed_wrap]; rfl

lemma levels (x : Site c) (U : Config G f) (y : Cover) :
    expandAt (S.ratio.embed (plank x y)) U=translate (centerRoot S.patch y) (expandAt (S.ratio.embed x) U) := by
  funext i; simp only [offsets, expandAt, Lattice.translate, map_add]; rw [add_assoc]

def macroR (P : Patch) := P.radius+4* P.L.val

lemma shifted (P : Patch) (y : Cover) (hy : y ∈ box 2) : P.sites.image (·+centerRoot P y) ⊆ box (macroR P) := by
  intro i he; obtain ⟨u,hu,rfl⟩ := mem_image.mp he
  obtain ⟨h,h'⟩ := box_test.mp hu
  obtain ⟨k,t⟩ := box_test.mp hy
  rw [box_test]; unfold centerRoot macroR; push_cast at *
  constructor <;> intro j <;> simp only [Pi.add_apply,Pi.mul_apply,Pi.natCast_apply, nsmul_eq_mul]
  all_goals nlinarith [k j,t j,h j,h' j]

lemma subline (P : Patch) (y : Cover) (hy : y∈box 2) (b : Axis) (k : ℕ) (hk : k≤P.L.val) : ∀ x∈ P.sites,
    x+centerRoot P y+k • step b ∈ box (macroR P) := by
  intro x hx
  obtain ⟨h,h'⟩ := box_test.mp hx; obtain ⟨m,n⟩ := box_test.mp hy
  simp only [box_test,macroR,centerRoot]; push_cast at *
  have hv : (k:ℤ)≤P.L.val := by exact_mod_cast hk
  constructor <;> intro j <;> simp only [Pi.add_apply,Pi.mul_apply,Pi.natCast_apply, nsmul_eq_mul,step_apply]
  all_goals split <;> nlinarith [h j,h' j,n j,m j]

lemma translator (H : Cover → G.El) (v : Cover) (U : CoverConfig G) :
    Lattice.gauge (fun z => H (z+v)) (translate v U)=translate v (Lattice.gauge H U) := by
  funext i; simp only [Lattice.gauge, Lattice.translate]; rw [add_right_comm]

def port (S : StepData c f) (x : Site c) (U : Config G f) := faces (box (macroR S.patch)) (expandAt (S.ratio.embed x) U)

def usable (U : Config G f) (x : Site c) (t : S.Choices) := ∀ y∈ box 2,
      0<S.patch.frameMass S.kernel (expandAt (S.ratio.embed (plank x y)) U) (t.1 (plank x y))

lemma wraps {U : Config G f} (t : S.Choices) (h : 0<S.likelihood U t) (x : Site c) : usable S U x t := by
  intro y _
  apply lt_of_le_of_ne ?_ ?_
  · unfold frameMass; split <;> positivity
  contrapose! h; rw [StepData.likelihood, Finset.prod_eq_zero (Finset.mem_univ (plank x y)) h.symm,zero_mul]

/-- constants after fixing only smoothing index, kernel/gauge. Produce any patch. -/
lemma planting (G : Gauge) (K : KernelChoices) (j : ℕ) : ∃ C D : ℝ, 0<C ∧ 0<D ∧
    ∀ (c f : Side) (S : StepData c f), K=S.kernel → j=S.patch.J →
      ∀ U : Config G f, ∀ x : Site c, ∀ t : S.Choices, usable S U x t → ∃ H : Cover → G.El, ∃ p : Cover → G.El,
        edges (box (macroR S.patch)) (Lattice.gauge H (expandAt (S.ratio.embed x) U)) ≤ D * S.patch.L.val * port S x U ∧
        ∀ y ∈ box 2,
          (∑ i : S.patch.Points, G.chord ((p y)⁻¹*S.frames U t.1 (plank x y) i* (H (i.val+centerRoot S.patch y))⁻¹)) ≤
            C*(S.patch.L.val:ℝ)^2*port S x U := by
  classical
  obtain ⟨A,hA,B⟩ := synchronized G
  let L : ℝ := 2*((j+3+4:ℕ):ℝ)+1
  let D : ℝ := 4*4*L
  let C := A*L*(D+K.axial_factor*L)
  have ha := K.axial_factor_pos
  have hk : 0<L := by unfold L; positivity
  have hd : 0<D := by unfold D; positivity
  refine ⟨C,D,by unfold C; positivity,hd,fun c f S he hx U x t hu => ?_⟩
  let R := macroR S.patch
  let V := expandAt (S.ratio.embed x) U
  let l := allAxes (1:Lattice.Order)
  obtain ⟨b,-,hb⟩ := existence l R 0 V ((List.nodup_finRange _).map (1:Lattice.Order).injective) (center_box _)
  have ht : slab R 0 l=box R := by
    have h (i : Axis) : i ∈ l := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    ext i; simp [slab_iff,h]
  let H := traveller l V b
  rw [ht, card_layers,show l.length=4 by simp [l,allAxes]] at hb; push_cast at hb
  have ht : faces (box R) V=port S x U := rfl
  have hn : 0≤port S x U := faces_nonneg ..
  have hs : 2*(R:ℝ)+1 ≤ L*S.patch.L.val := by
    have ht := carries j S.patch hx 4
    simpa only [Nat.cast_add,Nat.cast_mul,R,macroR,L,Nat.cast_ofNat,mul_comm _ (4:ℝ)] using ht
  have hg : edges (box R) (Lattice.gauge H V) ≤ D*S.patch.L.val*port S x U := by
    apply hb.trans; rw [ht]; apply mul_le_mul_of_nonneg_right _ hn; unfold D; linarith
  have hy : 2*(S.patch.radius:ℝ)+1 ≤ L*S.patch.L.val := by
    apply le_trans _ hs; gcongr; apply Nat.le_add_right
  let o (y : ↥(box 2)) := B S.patch K (t.1 (plank x y.val)) (expandAt (S.ratio.embed (plank x y.val)) U)
      (by rw [he]; exact hu y.val y.property) (fun z => H (z+centerRoot S.patch y.val))
  refine ⟨H,fun y => if h : y∈box 2 then (o ⟨y,h⟩).choose else 1,hg,fun y w => ?_⟩
  simp_rw [dif_pos w,StepData.frames, ← he]
  apply (o ⟨y,w⟩).choose_spec.trans
  let a := centerRoot S.patch y
  have h1 := (spread S.patch.sites (box R) a (shifted S.patch y w) (Lattice.gauge H V)).1
  have h2 := (spread S.patch.sites (box R) a (shifted S.patch y w) V).2
  simp_rw [levels,translator]
  let hP : ℝ := S.patch.L.val
  let s := translate a (Lattice.gauge H V)
  let u := translate a V
  change A*(2*S.patch.radius+1)*(edges S.patch.sites s+K.axial_factor*(2*S.patch.radius+1)*faces S.patch.sites u)≤_
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hy hA.le)
    (add_le_add (h1.trans hg) (mul_le_mul (mul_le_mul_of_nonneg_left hy ha.le) h2 (faces_nonneg ..) (by positivity)))
    (add_nonneg (edges_ge ..) (mul_nonneg (by positivity) (faces_nonneg ..))) (mul_nonneg hA.le (by positivity))) ?_
  rw [ht]; apply le_of_eq; unfold C; ring

lemma uloc (x : Site c) (y : Cover) (j : Axis) : plank x y+step j=plank x (y+step j) := by simp [plank,add_right_comm]

def pad (C : ℝ) (H : Cover → G.El) (x : Site c) (y : Cover) (U : Config G f) (u : G.El) (t : S.Choices) :=
    (∑ i : S.patch.Points,G.chord (u⁻¹*S.frames U t.1 (plank x y) i*(H (i.val+centerRoot S.patch y))⁻¹)) ≤ C*(S.patch.L.val:ℝ)^2*port S x U

lemma indicated (K T : ℝ) (U : Config G f) (x : Site c) (t : S.Choices) (y : Cover) (a : Axis) (hy : y∈box 2)
    (H : Cover → G.El) (ξ η : G.El) (hx : pad S K H x y U ξ t) (hη : pad S K H x (y+step a) U η t)
    (ht : edges (box (macroR S.patch)) (Lattice.gauge H (expandAt (S.ratio.embed x) U)) ≤ T*S.patch.L.val*port S x U) :
    (S.patch.L.val:ℝ)^2*G.chord (ξ⁻¹*S.prediction U t (plank x y,a)*η) ≤
      2*max 1 S.kernel.predictor_cut⁻¹ * (2*K+T)*port S x U := by
  let W := expandAt (S.ratio.embed x) U
  let v := centerRoot S.patch y
  let V := gauge H W
  let L := S.patch.L.val
  let d (i : S.patch.Points) := G.chord (travel V (i.val+v) (straight a L))
  let f (i : S.patch.Points) := ξ⁻¹*S.frames U t.1 (plank x y) i*(H (i.val+centerRoot S.patch y))⁻¹
  let g (i : S.patch.Points) := η⁻¹*S.frames U t.1 (plank x (y+step a)) i*(H (i.val+centerRoot S.patch (y+step a)))⁻¹
  let F := S.connector U t.1 (plank x y,a)
  have he (i : S.patch.Points) : G.chord (ξ⁻¹*F i*η) ≤ G.chord (f i)+d i+G.chord (g i) := by
    let M := S.repath a
    have he : straight a L = M := by simp [straight,L,M,StepData.repath,posDir]
    have ht := travel_gauge H W (i.val+v) M
    rw [S.stop_repath, show _ + S.patch.L.val • step a=i.val+centerRoot S.patch (y+step a) by unfold v centerRoot; rw [smul_add]; abel] at ht
    have eq : ξ⁻¹*F i*η=f i*travel V (i.val+v) M*(g i)⁻¹ := by
      change ξ⁻¹*(_*travel _ _ _*_)*η=_*travel (gauge H W) _ _*_
      unfold f g
      dsimp only
      rw [levels,← pull_one _ W,travel_pull,ht]
      simp only [affine, Signed.act_one]; simp_rw [Step.rotate_one]
      rw [uloc]
      simp only [List.map_replicate, v,M,StepData.repath]
      group
    rw [eq]; unfold d; rw [he]
    exact (G.chord_triangle _ _).trans (add_le_add (G.chord_triangle _ _) (G.chord_inv _).le)
  let l : ℝ := S.patch.L.val
  have hl : 0<l := by unfold l; positivity
  let α := 2*max 1 S.kernel.predictor_cut⁻¹
  change l^2*G.chord (ξ⁻¹*S.patch.predict _ _ _*η) ≤ α*_ * _
  let τ := ∑ i,S.patch.weight i * G.chord (ξ⁻¹*F i*η)
  apply le_trans (mul_le_mul_of_nonneg_left (price_query S.patch S.kernel F (t.2 (plank x y,a)) ξ η)  (by positivity))
  have hs (i) : l^4*(S.patch.weight i*G.chord (ξ⁻¹*F i*η)) ≤ G.chord (f i)+d i+G.chord (g i) := by
    apply le_trans _ (he i)
    rw [← mul_assoc,mul_comm (l^4)]
    exact (mul_le_mul_of_nonneg_right (light S.patch i) (G.chord_nonneg _)).trans_eq (one_mul _)
  have hi := traverse a S.patch V L v (box (macroR S.patch)) (subline S.patch y hy a)
  have hu : l^4*τ ≤ l^2*((2*K+T)*port S x U) := by
    unfold τ; rw [Finset.mul_sum]
    apply (Finset.sum_le_sum fun i _ ↦ hs i).trans
    simp_rw [Finset.sum_add_distrib]
    apply le_trans (add_le_add (add_le_add hx (hi.trans (mul_le_mul_of_nonneg_left ht hl.le))) hη)
    apply le_of_eq; unfold l L; ring
  rw [mul_left_comm]
  rw [mul_assoc α]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_mul_le_mul_left _ (show 0<l^2 by positivity)
  rw [← mul_assoc]; convert! hu using 1; ring

lemma corners {K : Type*} [Group K] (U : Links (Per c) K) (x : Site c) (p : PlaqAxes) : faceValue U (x,p)=
    U (x,p.val.1)*U (x+step p.val.1,p.val.2)*(U (x+step p.val.2,p.val.1))⁻¹*(U (x,p.val.2))⁻¹ := by
  unfold faceValue; simp [square, travel]
  rw [show x + step p.val.1 + step p.val.2 - step p.val.1=x+step p.val.2 by abel]
  group

def wire (U : Config G c) (V : Config G c) (e : Edge (Site c)) := G.chord (V e * (U e)⁻¹)

def fuel (U V : Config G c) (x : Site c) (p : PlaqAxes) :=
    wire U V (x,p.val.1)+wire U V (x+step p.val.1,p.val.2)+wire U V (x+step p.val.2,p.val.1)+wire U V (x,p.val.2)

lemma comp (U V : Config G c) (x : Site c) (p : PlaqAxes) : G.chord (faceValue V (x,p)) ≤
    G.chord (faceValue U (x,p))+fuel U V x p := by
  have he (x y a b : G.El) : G.chord ((x*y)*(a*b)⁻¹) ≤ G.chord (x*a⁻¹)+G.chord (y*b⁻¹) := by rw [show x*y*(a*b)⁻¹=(x*a⁻¹)*(a*(y*b⁻¹)*a⁻¹) by group]; exact (G.chord_triangle _ _).trans_eq (by rw [G.chord_conj])
  have h (x y : G.El) : G.chord (x⁻¹*y)=G.chord (x*y⁻¹) := by rw [chord_cyc, ← G.chord_inv (x*y⁻¹)]; simp only [mul_inv_rev,inv_inv]
  let X := faceValue U (x,p); let Y := faceValue V (x,p)
  have HH : G.chord (Y*X⁻¹)≤ fuel U V x p := by
    unfold fuel wire X Y
    rw [corners,corners]; apply (he ..).trans
    apply add_le_add
    · apply (he ..).trans
      apply add_le_add (he ..); rw [inv_inv,h]
    rw [inv_inv,h]
  change G.chord Y ≤ _
  rw [show Y=(Y*X⁻¹)*X by group]
  apply (G.chord_triangle _ _).trans; change _ ≤ G.chord X+_
  rw [add_comm (G.chord X)]; exact add_le_add_left HH _

/-- Need macro multiplicity/stencil clipping for spending reserve. -/
theorem qdc (G : Gauge) (K : KernelChoices) (j : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ (c f : Side) (S : StepData c f), K=S.kernel → j=S.patch.J →
    ∀ (U : Config G f) (V : Config G c) (x : Site c) (t : S.Choices),
    usable S U x t → ∀ p : PlaqAxes,
      G.chord (faceValue (S.prediction U t) (x,p)) ≤ C/(S.patch.L.val:ℝ)^2*port S x U ∧
      G.chord (faceValue V (x,p)) ≤ fuel (S.prediction U t) V x p+C/(S.patch.L.val:ℝ)^2*port S x U := by
  obtain ⟨C,D,hc,hd,h⟩ := planting G K j
  let a := 2*max 1 K.predictor_cut⁻¹ * (2*C + D)
  have ha : 0<a := by unfold a; positivity
  refine ⟨4*a,by positivity,fun c f S he ht U V x t hx p => ?_⟩
  obtain ⟨H,y,hE,H'⟩ := h c f S he ht U x t hx
  let l : ℝ := S.patch.L.val
  have hl : 0<l := by unfold l; positivity
  let z := a/l^2 * port S x U
  let Q := S.prediction U t
  have hh (u : Cover) (i : Axis) (hu : u ∈ box 2) (hi : u+step i ∈ box 2) :
      G.chord ((y u)⁻¹ * Q (plank x u,i)* y (u+step i)) ≤ z := by
    apply le_of_mul_le_mul_left _ (show 0<l^2 by positivity)
    apply le_trans (indicated S C D _ _ _ _ _ hu H _ _ (H' _ hu) (H' _ hi) hE)
    apply le_of_eq; unfold z a; rw [he]; field_simp
  let i := p.val.1; let k := p.val.2
  have hk (j : Axis) : step j ∈ box 2 := by
    rw [box_test]; constructor <;> intro h <;> rw [step_apply] <;> split <;> norm_num
  have hv : (step i : Cover)+step k∈box 2 := by
    rw [box_test]; constructor <;> intro h <;> simp only [Pi.add_apply,step_apply] <;> split <;> split <;> norm_num
  have ha (s) : plank x (step s)=x+step s := by simp [plank,add_comm]
  have hb := hh 0 i (center_box _) (by rw [zero_add]; exact hk _)
  have hg := hh 0 k (center_box _) (by rw [zero_add]; exact hk _)
  have hn := hh (step i) k (hk _) hv
  have hu := hh (step k) i (hk _) (by rw [add_comm]; exact hv)
  rw [ha _] at hn; rw [ha _,add_comm (step k : Cover)] at hu
  simp only [plank,map_zero,zero_add] at hb hg
  have hR : G.chord (faceValue Q (x,p)) ≤ 4*z := by
    rw [← G.chord_conj (y 0)⁻¹,inv_inv,corners]
    rw [show (y 0)⁻¹ * (Q (x,p.val.1)*_*_*_) * y 0 =
      ((y 0)⁻¹*Q (x,i)*y (step i))*((y (step i))⁻¹*Q (x+step i,k)*y (step i+step k))*
      ((y (step k))⁻¹*Q (x+step k,i)*y (step i+step k))⁻¹*((y 0)⁻¹*Q (x,k)*y (step k))⁻¹ by unfold i k; group]
    apply (G.chord_triangle _ _).trans
    rw [G.chord_inv]
    refine (add_le_add (le_trans (G.chord_triangle _ _) ?_) hg).trans_eq (show (z+z)+z+z=4*z by ring)
    rw [G.chord_inv]; exact add_le_add ((G.chord_triangle _ _).trans (add_le_add hb hn)) hu
  have hq : G.chord (faceValue Q (x,p)) ≤ 4*a/l^2*port S x U := hR.trans_eq (by unfold z; ring)
  exact ⟨hq,(comp Q V _ _).trans ((add_le_add_left hq (fuel Q V x p)).trans_eq (add_comm ..))⟩
end YM.Pressure
