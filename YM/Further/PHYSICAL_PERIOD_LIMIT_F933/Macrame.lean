import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Shingle
import YM.Next.FLUCTUATIONS.Kernel
import YM.Work.A05


/-!
# covers of periods: (actual centered-subdivision roots)

Includes orbit multiplicities and path sales on full labels. Windows don't need
to start at 0. Require nontrivial coarse side for replica crossings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Macrame
open Push.Uniform Precision Function Shingle Lattice Gauge Tree RG Wilson Exterior Filter Finset Set
open scoped BigOperators Topology Classical

variable {c C f F n N : Side}

def splitter (h : n.val ∣ N.val) : Site N →+ Site n :=
    { toFun := fun x i=>ZMod.castHom h (Per n) (x i)
      map_zero' := by ext; simp
      map_add' := fun x y => funext fun i=> (ZMod.castHom h (Per n)).map_add .. }
lemma branch (h : n.val∣ N.val) (j : Cover) : splitter h (wrap N j) = wrap n j := funext fun _ => map_intCast (ZMod.castHom h (Per n)) _
lemma seeds (h : n.val∣ N.val) : Surjective (splitter h) := fun x => ⟨wrap N (lift x), (branch ..).trans (wrap_lift x)⟩

lemma blocks_at_floor (h : n.val ∣ N.val) : Reserved id (splitter h) n.val := by
  constructor
  intro i j he hJ
  have hx : wrap n (lift (i-j))= (0:Site n) := by rw [← branch h,wrap_lift,map_sub,he,sub_self]
  obtain ⟨a,ha⟩ : ∃ a : Axis, lift (i-j) a≠0 := by
    by_contra! h; have he : lift (i-j)=0 := funext h; have hh := congr_arg (wrap N) he; rw [wrap_lift,map_zero] at hh; exact hJ (sub_eq_zero.mp hh)
  have h0 := congr_fun hx a
  have hy : (n.val : ℤ)∣ -(lift (i-j) a) := by
    rw [← zero_sub]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp ((by rw [Int.cast_zero]; exact h0) : ((lift (i-j) a:ℤ):ZMod n.val)=(↑(0:ℤ):ZMod n.val))
  have hy : (n.val:ℤ)∣ lift (i-j) a := (dvd_neg ..).mp hy
  have hN : n.val∣(lift (i-j) a).natAbs := by obtain ⟨k,hk⟩:= hy; refine ⟨k.natAbs,?_⟩; rw [hk]; rw [Int.natAbs_mul]; rfl
  exact le_trans (Nat.le_of_dvd (by omega) hN) ((component_le ..) : (lift (i-j) a).natAbs ≤ pdist (i-j))

-- a window maps from possibly larger to smaller sites, size of fibre M and carries any anchored path by its whole physical offset
structure Window (x y : Side) (M : ℕ) where
  cut : Site y → Site x
  rooted (i : Site y) (v : Cover) : cut (wrap y v + i)=wrap x v + cut i
  fold : Fold cut M

variable {Y Z : Side} {M : ℕ}
lemma basefold (h : n.val∣N.val) (hx : N.val=n.val*M) : Fold (splitter h) (M^4) := by
  let p := splitter h
  let q := (parcel p 0).card
  have he (i : Site n) : (parcel p i).card=q := by
    obtain ⟨x,hx⟩:= seeds h i
    let E := Equiv.addRight x
    have hh : parcel p i=(parcel p 0).map E.toEmbedding := by
      subst i; ext j
      simp only [Finset.mem_map, Equiv.toEmbedding_apply, posted]
      constructor
      · intro hj; exact ⟨j-x,by rw [map_sub,hj, sub_self],by change j-x+x=j; abel⟩
      rintro ⟨a,ha,rfl⟩; change p (a+x)=_; rw [map_add,ha,zero_add]
    rw [hh]; exact Finset.card_map _
  have hu := received _ he
  have H : q=M^4 := by
    rw [site_card,site_card,hx,mul_pow,mul_comm] at hu; exact Nat.eq_of_mul_eq_mul_right (pow_pos n.property _) hu.symm
  exact H ▸ he

def normal (h : n.val ∣ N.val) (hx : N.val=n.val*M) : Window n N (M^4) := ⟨splitter h, fun i w=>by rw [map_add,branch],basefold h hx⟩

def parallel (w : Site n) : Window n n 1 where
  cut x:= x+w
  rooted _ _ := by abel
  fold i := by
    rw [show parcel (fun x : Site n=>x+w) i = {i-w} by ext; simp only [posted, Finset.mem_singleton]; exact eq_sub_iff_add_eq.symm]
    rfl

namespace Window
variable (G : Window n N M)
lemma port (x : Site N) (v : Cover) : G.cut (x + wrap N v) = G.cut x + wrap n v := by rw [add_comm x,G.rooted,add_comm]
lemma step_up (x : Site N) (d : Axis) : G.cut (x+step d) = G.cut x + step d := by rw [← wrap_step N,port,wrap_step]
lemma step_down (x : Site N) (d : Axis) : G.cut (x-step d)=G.cut x - step d := by
  rw [show x-step d=x+(-step d) by rw [sub_eq_add_neg],← wrap_step N,← map_neg,port,map_neg,wrap_step,sub_eq_add_neg]
lemma uniform (x : Site N) (d : Step) : G.cut (x+d.vec) = G.cut x + d.vec := by rw [← wrap_vec N,port,wrap_vec]
lemma used (x : Site N) (d : Step) : Prod.map G.cut id (d.used x)=d.used (G.cut x) := by
  unfold Step.used; split
  · change (G.cut (x-step d.dir),d.dir)=(G.cut x-step d.dir,d.dir); rw [step_down]
  rfl

-- Natural across all actual link arrays
variable {g : Gauge}
abbrev links (U : Config g n) : Config g N := fun x=> U (G.cut x.1,x.2)
@[simp] lemma read (i : Site N) (U : Config g n) (d : Step) : d.read (G.links U) i=d.read U (G.cut i) := by
  unfold Step.read; split
  · change (U (Prod.map G.cut id _))⁻¹= _; rw [G.used]
  change U (Prod.map G.cut id _)=_; rw [G.used]
lemma traveller (U : Config g n) (i : Site N) (v : Walk) : travel (G.links U) i v=travel U (G.cut i) v := by
  induction v generalizing i with
  | nil => rfl
  | cons d v hv => rw [travel,read,hv,uniform,← travel]
lemma expansion (i : Site N) (U : Config g n) : expandAt i (G.links U)=expandAt (G.cut i) U := by
  funext e; unfold expandAt links; rw [G.rooted]

-- signed Path actions: set weights translated by window s^-1 G s on sites

def sign (s : Signed) : Window n N M where
  cut i:= s⁻¹.act (G.cut (s.act i))
  rooted i z := by
    rw [s.act_add,wrap_signed,G.rooted,s⁻¹.act_add,wrap_signed]; congr 1; rw [← Signed.act_mul, inv_mul_cancel,Signed.act_one]
  fold i := by
    let F : Site N ≃+ Site N := s.actEquiv
    let P : Site n ≃+ Site n := s⁻¹.actEquiv
    have hF : parcel (⇑P ∘ (G.cut ∘ F)) i=(parcel G.cut (P.symm i)).map F.symm.toEquiv.toEmbedding := by
      ext j; simp only [posted,Function.comp_apply,Finset.mem_map,Equiv.toEmbedding_apply, ]
      constructor
      · intro hj
        exact ⟨F j,by rw [← hj, P.symm_apply_apply],F.symm_apply_apply _⟩
      rintro ⟨q,hq,rfl⟩; change P (G.cut (F (F.symm q)))=_; rw [F.apply_symm_apply,hq, P.apply_symm_apply]
    change (parcel (⇑P ∘ (G.cut ∘ F)) i).card=_
    rw [hF,Finset.card_map]; exact G.fold _
lemma signed (s : Signed) (U : Config g n) : pull s 0 (G.links U)=(G.sign s).links (pull s 0 U) := by
  funext x
  unfold pull links
  change ((posDir _).rotate s).read (G.links U) _ = _
  rw [read]; simp only [affine,add_zero,sign]; rw [← Signed.act_mul,mul_inv_cancel,Signed.act_one]

lemma quadratic_price (P : Clip) (R : PathData g) (U : Config g n) : quadratic P R (G.links U)=(M:ℝ)*quadratic P R U := by
  have hz i (d : PlaqAxes) : faceValue (G.links U) (i,d) = faceValue U (G.cut i,d) := G.traveller ..
  have hv i (d : PlaqAxes) : R.ell (G.links U) (i,d) = R.ell U (G.cut i,d) := by
    unfold PathData.ell PathData.ellTerms Slot.atSite; rw [show expandAt i (G.links U)=_ from G.expansion ..] -- dsimp
  unfold quadratic; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp_rw [hz,hv]; have h := multiplied G.cut G.fold (fun i:Site n => ∑ p:PlaqAxes,(P.direct*g.price (faceValue U (i,p)) + ‖R.ell U (i,p)‖^2/2)); simpa only [nsmul_eq_mul] using h
lemma unc {k : ℕ} (A : ℕ→Atom g k) (U : Config g n) : uncut A (G.links U)=(M:ℝ)*uncut A U := by
  have he i (z : Site N) : (A i).unmasked (G.links U) z=(A i).unmasked U (G.cut z) := by
    unfold Atom.unmasked Slot.atSite; rw [expansion]
  unfold uncut; simp_rw [he]; simpa only [nsmul_eq_mul] using (multiplied G.cut G.fold (fun z:Site n=>∑' i,(A i).unmasked U z))
lemma revenue (P : Clip) (R : PathData g) (U : Config g n) : mainTerm P R (G.links U)=(M:ℝ)*mainTerm P R U := by
  unfold mainTerm Patch.average; rw [← mul_assoc, mul_comm (M:ℝ), mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; simp_rw [G.signed]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Window.quadratic_price,Window.unc, mul_add])
end Window
end YM.Further.PhysicalPeriodLimitF933.Macrame
