import YM.TraceExtension.Perfect.Sheaf

/-!
# Arithmetic division by difference. No inverse on lattice frequencies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Lattice Laurent RG Wilson Function Finset Filter
open scoped BigOperators Topology
namespace Sheaf
variable {A:Type*} [AddCommGroup A] [Module ℝ A]
def Runs (a:Axis): Sheaf→ Prop
| stay=>True
| mon z=>∃ i:ℤ,z=i • (step a:Cover)
| scale _ X=>Runs a X
| duo X Y=>Runs a X ∧ Runs a Y
| mix X Y=>Runs a X ∧ Runs a Y
lemma disk_runs {i:ℤ}(a:Axis)(n:ℕ): Runs a (disk (i • step a) n):=by
 induction n with
 | zero=>trivial
 | succ n h=>refine ⟨h,(n:ℤ)*i,?_⟩; rw [mul_smul]; simp
lemma little_runs {i:ℤ}(a:Axis)(n:ℕ): Runs a (little (i • step a) n):=⟨⟨-(n:ℤ)*i,by rw [mul_smul]; simp⟩,disk_runs ..⟩
lemma band_runs {i:ℤ}(a:Axis): Runs a (band (i • step a)):= ⟨⟨little_runs ..,little_runs ..⟩,little_runs ..,little_runs ..⟩

lemma draw (X:Sheaf) (a:Axis)(h : Runs a X):∃ Y: Sheaf,Y.radius ≤ X.radius*3 ∧ Y.debt ≤ X.radius*X.debt ∧ ∀ f:Cover→A,take (take f Y) (Δ (step a))=take f X-X.gold • f:=by
 induction X with
 | stay=> exact ⟨stay,by simp [radius],by simp [debt], fun f=> funext fun x => by simp [rises,take,gold]⟩
 | mon z=>
    obtain ⟨i,rfl⟩:= h; cases i with
    | ofNat k=>
     obtain ⟨h,p,v⟩:=disk_cost (step a) k; refine ⟨disk (step a) k,?_,?_,fun f=>?_⟩
     · have hz : size (Int.ofNat k • (step a:Cover))=k:=by simp [size,Pi.smul_apply,apply_ite (fun z:ℤ=>z.natAbs),mul_ite];
       rw [radius,hz]; exact h.trans (by rw [size_step_one]; omega)
     · have hz : size (Int.ofNat k • (step a:Cover))=k:=by simp [size,Pi.smul_apply,apply_ite Int.natAbs,mul_ite]
       rw [debt,radius,hz,p,mul_one]
     rw [show take (take f (disk (step a) k)) _= _ from disk_step _ f k]; ext1 x; rw [rises]; simp [take,gold]
    | negSucc k=>
     let v:Cover:= (k+1) • step a
     let Y:= mix (scale (-1) (mon (-v))) (disk (step a) (k+1))
     obtain ⟨h,p,d⟩:=disk_cost (step a) (k+1); rw [size_step_one,mul_one] at h
     have hu:Int.negSucc k • (step a:Cover)= -v:=by rw [Int.negSucc_eq]; simp [v]; ring
     have hx:size (-v)=k+1:=by rw [← hu]; simp [size,Pi.smul_apply,apply_ite Int.natAbs,mul_ite]
     rw [hu]; refine ⟨Y,?_,?_,fun f=>?_⟩
     · simp only[Y,radius,hx]; omega
     · simp [Y,radius,hx,debt,p]
     dsimp only [Y]; rw [take,take,take,smul_f, rope (Δ (step a))]; change (-1:ℝ) • take (take (take f (disk (step a) (k+1))) _) (mon (-v))=_
     rw [show take (take f (disk (step a) (k+1))) _= _ from disk_step _ f (k+1)]; ext1 x; simp only [Pi.sub_apply,Pi.smul_apply,take,gold]
     rw [rises]; simp [v]
 | scale c X h'=>
    obtain ⟨Y,hy,hv,H⟩:=h' h
    refine ⟨scale c Y,hy,?_ , fun f=> ?_⟩
    · simpa only [debt,radius,mul_left_comm |c|] using mul_le_mul_of_nonneg_left hv (abs_nonneg c)
    simp only [take,gold,smul_f,H,smul_sub,smul_smul]
 | duo X Y h' p'=>
    obtain ⟨V,ht,he,H⟩:= h' h.1; obtain ⟨Z,hx,hp,P⟩:=p' h.2
    refine ⟨duo V Z,?_,?_,fun f=> ?_⟩
    · simp only [radius]; omega
    · have hV : X.radius ≤ (X.duo Y).radius:= le_max_left ..; have hY : Y.radius ≤ (X.duo Y).radius:= le_max_right ..
      rw [debt,show (X.duo Y).debt=_ from rfl]; change _ ≤ ((X.duo Y).radius:ℝ)*(X.debt+Y.debt); rw[mul_add]
      exact add_le_add (he.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hV) X.debt_pos)) (hp.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hY) Y.debt_pos))
    simp only [take,gold,add_f,H,P,add_smul]; abel
 | mix X Y h' p'=>
    obtain ⟨V,ht,he,H⟩:= h' h.1; obtain ⟨Z,hx,hp,P⟩:=p' h.2
    have hl : |X.gold| ≤ X.debt:=by
       clear H h' he h ht; induction X with
       | stay=>simp [debt,gold]
       | mon=>simp [debt,gold]
       | scale c x h=>rw[debt,gold,abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
       | duo x y h p=>exact (abs_add_le ..).trans (add_le_add h p)
       | mix x y h p=>rw [debt,gold,abs_mul]; exact mul_le_mul h p (abs_nonneg _) (x.debt_pos)
    refine ⟨duo (mix V Y) (scale X.gold Z),?_,?_,fun f=>?_⟩
    · simp only [radius]; omega
    · have ht:= add_le_add (mul_le_mul_of_nonneg_right he Y.debt_pos) (mul_le_mul hl hp Z.debt_pos X.debt_pos)
      simp only [debt,radius,Nat.cast_add]; exact ht.trans_eq (by ring)
    simp only [take,gold,add_f,smul_f, H,P,smul_sub,smul_smul]; abel

variable (L:Side)
def ply (a:Axis):=scale ((L.val:ℝ))⁻¹ (disk (step a) L.val)
lemma ply_level (a:Axis): (ply L a).debt=1 ∧ (ply L a).gold=1 ∧ (ply L a).radius ≤ L.val:= by
 have ht:0<(L.val:ℝ):= Nat.cast_pos.mpr L.property
 obtain ⟨hv,h,p⟩:=disk_cost (step a) L.val; rw [size_step_one,mul_one] at hv; change _ ∧ _ ∧ _; simp [ply,debt,gold,h,p,radius,hv,ht.ne']
lemma ply_step (a:Axis)(f:Cover→A): take (take f (ply L a)) (Δ (step a))= ((L.val:ℝ))⁻¹ • take f (Δ (L.val • step a)):=by rw [ply,take,smul_f,show take (take f (disk (step a) L.val)) _=_ from disk_step _ f L.val]

def nigh (a:Axis):= mix (band (L.val • step a)) (ply L a)
def boil (a:Axis) := mix (ply L a) (nigh L a)
lemma nigh_fee (a:Axis): (nigh L a).radius ≤ 13*L.val ∧ (nigh L a).debt ≤ 32 ∧ (nigh L a).gold=1:= by
 obtain ⟨h,x,y⟩:= band_fee (L.val • step a); obtain ⟨p,v,t⟩:= ply_level L a
 have hb:= size_nsmul (step a) L.val; rw [size_step_one,mul_one] at hb
 refine ⟨by simp only[nigh,radius];omega, ?_,?_⟩
 · simpa only [nigh,debt,p,mul_one] using y
 simp only [nigh,gold,h,v,one_mul]
lemma boil_price (a:Axis): (boil L a).radius ≤ 14*L.val ∧ (boil L a).debt ≤ 32 ∧ (boil L a).gold=1:=by
 obtain ⟨p,h,x⟩:= nigh_fee L a; obtain ⟨v,t,y⟩:= ply_level L a
 refine ⟨by simp only[boil,radius];omega,?_,?_⟩
 · simpa only [boil,debt,v,one_mul] using h
 simp only [boil,gold,x,t,one_mul]
end Sheaf
end YM.Trace.Perfect
