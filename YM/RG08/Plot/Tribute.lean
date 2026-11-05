import YM.RG08.Plot.Fields
/-!
# Reading spacing and root budgets at profile roots
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff Classical
variable {I J Y:Type}{m b i K D t r:ℕ}{L:Side} {z a:Cover}{p:Site L}{v θ R A:ℝ}{x w:E4}{G:Gauge}{X: Chain}{g:Exam D}
def stemA (L:Side)(y:Cover)(p:Site L):= L.val • y+Lattice.lift p
def growP (L:Side)(z:Cover):= Work.F08.carry (0:Site L) z
def growL (L:Side)(z:Cover):= Work.F08.arrives (0:Site L) z
lemma nil_root (p:Side): Lattice.lift (0:Site p)=0:= by ext; simp [Lattice.lift]
lemma grows (L:Side)(z:Cover): stemA L (growP L z) (growL L z)=z := by have h:= carry_spec (0:Site L) z; rw [nil_root,zero_add,add_comm] at h; exact h.symm
lemma stemA_fit (L:Side)(w:Cover × Site L): growP L (stemA L w.1 w.2)=w.1 ∧ growL L (stemA L w.1 w.2)=w.2:= by
   rcases w with ⟨i,b⟩; dsimp only
   have hx : growL L (stemA L i b)=b:= by
     unfold growL Work.F08.arrives; rw [nil_root,zero_add,stemA,map_add,map_nsmul,wrap_lift]; have hp: L.val • wrap L i=0:= by ext; simp [nsmul_eq_mul,Per]
     rw [hp,zero_add]
   refine ⟨?_,hx⟩; have h:= grows L (stemA L i b); rw [hx] at h
   ext1 k; apply mul_left_cancel₀ (show (L.val:ℤ)≠0 by positivity); simpa only [Pi.smul_apply,nsmul_eq_mul] using congr_fun (add_right_cancel (show L.val • growP L _ + Lattice.lift b=L.val • i+Lattice.lift b from h)) k
lemma spanned (X:Chain)(K i:ℕ)(x:E4): stemA (X.S.block i) (arcT X K i x) (shrinkP X K i x)=arcT X K (i+1) x:= by unfold stemA; rw [arena]; abel
lemma seats_root (k:ℕ)(z:Cover): Place.seat (k•z)=(k:ℝ)•Place.seat z := by induction k with | zero=> simp| succ k ih=> rw [succ_nsmul,Place.seat_add,ih,Nat.cast_add_one,add_smul,one_smul]
lemma rolls_in (h:v=θ*L.val)(p:Site L)(w:E4) (x:E4)(z:Cover):
    stud v x z + v • (spinner p+(L.val:ℝ)⁻¹ • w)= stud θ x (stemA L z p)+θ • w := by
   unfold stud spinner stemA; rw [h,Place.seat_add,seats_root]; simp_rw [smul_add,smul_smul]; rw [mul_assoc θ, mul_inv_cancel₀ (by positivity : (L.val:ℝ)≠0),mul_one]; abel
lemma retest (h:v=θ*L.val)(p:Site L)(g:Exam D) (z:Cover): Pages.roll (spinner p) (L.val:ℝ)⁻¹ (exteriorP g v x z)= exteriorP g θ x (stemA L z p) := Subtype.ext (funext fun i=> congr_arg (g.val) (rolls_in h p i x z))
lemma costP (n:ℕ) (Y:E4) (h:∀ i, ‖Y i‖≤ R): ‖Y‖ ≤ 4*R := by
   have hp : Y=∑ a:Axis,Y a • basis a := by ext; simp
   have ht:= norm_sum_le (univ: Finset Axis) (fun a=> Y a • basis a)
   refine (le_of_eq (congr_arg (fun x:E4=>‖x‖) hp)).trans (ht.trans (le_trans (Finset.sum_le_sum (g:=fun _=> R) ?_) ?_))
   · intro i _; simp_rw [norm_smul]; simpa [basis] using h i
   simp [Axis]
lemma stem_dist (a b:Cover) : ‖Place.seat a-Place.seat b‖ ≤ size (a-b) := by
   let Y:=Place.seat a-Place.seat b; have hp:Y=∑ i:Axis,Y i • basis i:= by ext; simp
   apply le_trans (b:= ∑ i:Axis, ‖Y i • basis i‖) ?_ _
   · rw [← show ‖Y‖=‖Place.seat a-Place.seat b‖ from rfl]; exact (le_of_eq (congr_arg (fun x:E4=>‖x‖) hp)).trans (norm_sum_le ..)
   unfold Laurent.size; rw [Nat.cast_sum]; apply sum_le_sum; intro k _; change ‖((a k:ℤ)-(b k:ℝ)) • basis k‖ ≤ _; simp_rw [norm_smul,show ‖basis k‖=1 by simp [basis],mul_one,←Int.cast_sub,signed_norm]; rfl
lemma descendant (h:1/2≤R) (hp:reached g x (spanP X K (i+1)) R z): reached g x (spanP X K i) R (growP (X.S.block i) z):= by
   obtain ⟨w,hw⟩:=hp; let L:=X.S.block i; let p:=growL L z; let A:= growP L z; let V:=spinner p+(L.val:ℝ)⁻¹ • w.val
   refine ⟨⟨V,(nesting p (X.S.block_odd i) h).covers w.property⟩,?_⟩; change stud _ _ (growP L _) + _ • V ∈ _; unfold V; rw [rolls_in (spanP_tick X K i|>.symm) p,show stemA L (growP L z) p=z from grows ..]; exact hw
-- native support in full coarse mesh. True projection distances near separation.
def Resolve (g f:Exam D)(u:ℝ):Prop:= ∀ x∈tsupport g.val,∀ y∈tsupport f.val, 1≤ u*‖x-y‖
lemma outskirt {g f: Exam D}{u:ℝ}{A C:Cover} (hp: reached g x θ R A) (ht:reached f x θ R C) (hh: Resolve g f u)(hv:0≤u)(he:0 ≤ θ): 1≤ (u*(1+8*R))*θ*(1+(size (A-C):ℝ)):= by
   obtain ⟨w,hw⟩:=hp; obtain ⟨b,hb⟩:=ht; let P:=stud θ x A+θ • w.val; let Q:=stud θ x C+θ • b.val
   have hR:0≤R:= (norm_nonneg (w.val (0:Axis))).trans (w.property _)
   have hY:= costP 0 w.val w.property; have hB:= costP 0 b.val b.property
   have hP: ‖P-Q‖ ≤ θ*(size (A-C)+4*R+4*R) := by
     rw [show P-Q=θ • (Place.seat A-Place.seat C+w.val-b.val) from (by unfold P Q stud; rw [smul_sub,smul_add,smul_sub]; abel),norm_smul,Real.norm_of_nonneg he]
     apply mul_le_mul_of_nonneg_left _ he; exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (stem_dist ..) hY)) hB)
   apply (hh _ hw _ hb).trans
   apply (mul_le_mul_of_nonneg_left hP hv).trans; let S:=(size (A-C):ℝ); have hz:0 ≤ S:= by unfold S; positivity
   change u * (θ*(S+_+_)) ≤ _ * θ*(1+S)
   nlinarith only [show 0≤ u*θ by positivity, show 0 ≤ u*θ*R*S by positivity]
lemma royalty (X:Chain) (i p:ℕ) x z :
    let Q:=growP (X.S.block i) z
    Lattice.lift (shrinkP X p i x)+(z-arcT X p (i+1) x)= (X.S.block i).val • (Q-arcT X p i x)+Lattice.lift (growL (X.S.block i) z):= by
  intro Q; rw [arena,smul_sub]; have hp : z= _ := (grows (X.S.block i) z).symm; change z=(X.S.block i).val • Q+Lattice.lift (growL (X.S.block i) z) at hp
  conv_lhs => arg 2; lhs; rw [hp]; -- inside
  abel
lemma native_fee {D:ℕ}(g:Profile D)(x:E4)(X:Chain)(A R:ℝ)(k i:ℕ)(hz:0≤A)(h:0≤R)(hp:Spatial g.val A)(he:spanP X k i≤1)(z:Cover)(hw:z ∈ blush g X k i x R): spanP X k i*(size (z-arcT X k i x):ℝ)≤4*(2+R+A):= by
   let p:=spanP X k i; have hu: 0<p:=spanP_pos ..; have hZ:= linkP hp (blush_v.mp hw); have hP:= circle_fin hz h hu he
   change p*_ ≤ _
   apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hZ) hu.le).trans
   push_cast; dsimp only [p] at *; linarith
end YM.RG08.Plot
