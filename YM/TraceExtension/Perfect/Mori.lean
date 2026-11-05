import YM.TraceExtension.Perfect.Tael
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {P:Patch}{Z:KernelChoices}{p:Clip}{G:Gauge}{μ A α B D H ι η u v C:ℝ} {V:Type}{F:Filter V}{n:ℕ}
set_option quotPrecheck false
variable {X: V→ Slide G P Z p μ A α B}
local notation "LX" => (P.L.val:ℝ)
local notation "f_"=>fun w=>(X w).f
local notation "c_"=>fun w=>(X w).c
local notation "r_"=>fun w=>(X w).s.ratio

variable {J:∀ w:V,Site (X w).f → Acr G (X w).f→ℝ}{K:∀ w,Site (X w).f→Acr G (X w).c→ℝ}
variable (s:LotFee F X u v H D)(ℓ:Tour X J K)
namespace Tour
variable (X K) in
def ill (q:ℕ)(S:Sheaf)(w:V):= LX^q • verse S (X w).s.ratio (K w)
def allSheaf:ℝ:=32^8
lemma sheaf_debt_pos:0<allSheaf:=by unfold allSheaf; positivity
-- relative earnings per position (core & projection, after transport)
include s ℓ
lemma ink (G':Tit G→Tit G→ℝ)(S:Sheaf)(hU:S.gold=1)(q:ℕ)(V:ℝ)(hV:0 ≤ V)(hg:∀ i j,ScoreG i+ScoreG j<q→G' i j=0)
  (hp:∀ y,Tip F y (fun w=> J w (y w)) G' q)(he:∀ y,Ear F y (fun w=>J w (y w)) v 2 V)(x:∀ w,Site (X w).c):Tip F x (fun w=> ill X K q S w (x w)) G' q:=by
    let p:=((P.L.val:ℝ))⁻¹^q
    let f(w)(j:Cover):= K w ((r_ w).embed (x w)+wrap _ j)
    have ht:= S.top x (p • G') f 0 (fun w=>ℓ.be s x w hV q G' hg (he _) (hp _)); have h': (fun w=> S.take (f w) 0)=(fun w=> verse S ((X w).s.ratio) (K w) (x w)):=rfl
    rw [h',hU,one_smul] at ht
    have hv:= ht.grind (LX^q); rw [smul_smul, show LX^q*p=1 from by unfold p; rw [← mul_pow, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp P.L.property)),one_pow],one_smul] at hv; exact hv

omit s ℓ in
lemma bill (j n:ℕ)(S:Sheaf)(h:S.radius ≤ 140*P.L.val)(hu:S.debt ≤ allSheaf)(C:ℝ)(hv:0 ≤ C)(x:∀ w,Site (X w).c)(he:∀ q:Cover,size q ≤ 140*P.L.val→ Ear F x (fun w=>K w ((X w).s.ratio.embed (x w)+wrap _ q)) u n C): Ear F x (fun w=>ill X K j S w (x w)) u n ((P.L.val:ℝ)^j * allSheaf * C):=by
 let f w (q:Cover):= K w ((X w).s.ratio.embed (x w)+wrap _ q)
 have ht:= S.ear x f 0 0 (fun b hb=> he b ((show size b ≤ _ from ?_).trans h)); rotate_left
 · simpa only[size,Pi.zero_apply,Int.natAbs_zero, Finset.sum_const_zero, zero_add] using hb
 have hx:0 ≤ (P.L.val:ℝ):= by positivity
 rw[mul_assoc];have hV:=(ht.up (mul_le_mul_of_nonneg_right hu hv)).grind ((P.L.val:ℝ)^j); rw [abs_of_nonneg (pow_nonneg hx j)] at hV; exact hV
local notation "S$"=> allSheaf
local notation "cₗ"=> 2^13*H^2
lemma lvl2 (C:ℝ)(hx:0 ≤ C)(hp:∀ y,Ear F y (fun w=>J w (y w)) v 2 C)(x:∀ w,Site (X w).c)(b:Cover)(he:size b ≤ 140*P.L.val): Ear F x (fun w=>K w ((r_ w).embed (x w)+wrap _ b)) u 2 ((cₗ/LX^4)*C):=by
 let f(i:ℕ):ℝ:= if i=2 then C else 0
 have hy:= ℓ.boon s x b he 2 le_rfl (by norm_num) f (fun i=>by unfold f;split <;> linarith) (fun k hk h=>by rw [le_antisymm hk h]; exact hp _); rw [Finset.sum_eq_zero,add_zero] at hy; swap
 · intro i h; have hp:i.length ≠ 2:=fun hu=> (mem_erase.mp h).1 (Planned.PrimaryIntegral295.Cases.finest i hu); simp [f,hp]
 have hL : LX>0:=side_pos _; refine hy.up (mul_le_mul_of_nonneg_right ?_ hx)
 norm_num; rw [div_pow, ← pow_mul]; norm_num; gcongr; nlinarith [sq_nonneg H]
-- simplified margin coefficient
lemma boolJ (T:Tit G→Tit G→ℝ)(h:∀ y,Tip F y (fun w=>J w (y w)) T 4)
   {K' J'}(hp: Tour X J' K')(ht:∀ y,Tip F y (fun w=>J' w (y w)) T 4)(A B':ℝ)(hv:0≤A)(hB: 0 ≤ B')
   (hK:∀ y,Ear F y (fun w=>J' w (y w)) v 2 A)(hJ:∀ y,Ear F y (fun w=> J w (y w)) v 2 B')
   (x:∀ w,Site (X w).c)(q:Cover)(hb:size q ≤ 140*P.L.val): Ear F x (fun w=>K w ((r_ w).embed (x w)+wrap _ q)) u 2 (((2^13*H^2/LX^4)*A)+((cₗ/LX^5)*(B'+A))):=by
    let y w:= (r_ w).embed (x w)+wrap _ q
    have hz:= (h y).except (ht y); rw[sub_self] at hz
    have he:= hp.lvl2 s A hv hK x q hb; have hm:= (ℓ.away hp).bear s x q hb ((hJ y).except (hK y)) hz
    exact (he.plus hm).likewise (fun w=> Filter.EventuallyEq.of_eq (add_sub_cancel ..))
lemma boolY (T:Tit G→Tit G→ℝ)(hU:∀ i j,ScoreG i+ScoreG j<5→T i j=0)(h:∀ y,Tip F y (fun w=>J w (y w)) T 5)
   {K' J'}(hp: Tour X J' K')(ht:∀ y,Tip F y (fun w=> J' w (y w)) T 5)(A B':ℝ)(hv:0≤A)(hB:0≤B')
   (hK:∀ y,Ear F y (fun w=>J' w (y w)) v 2 A)(hJ:∀ y,Ear F y (fun w=>J w (y w)) v 2 B')(x:∀ w,Site (X w).c)(q:Cover)(hb:size q≤ 140*P.L.val): Ear F x (fun w=>K w ((r_ w).embed (x w)+wrap _ q)) u 2 ((cₗ/LX^5)*A+(cₗ/LX^6)*(B'+A)):=by
    let y w:= (r_ w).embed (x w)+wrap _ q
    have hx := (h y).except (ht y); rw[sub_self] at hx
    have hy: Tip F y (fun w=>J' w (y w)) 0 4:=⟨(hK y).h,⟨fun i j hh=> (by have he:= (ht y).sees.taste i j (by omega); rw [hU i j (by omega)] at he; exact he)⟩⟩
    have he:= hp.bear s x q hb (hK y) hy
    have hz:= (ℓ.away hp).boar s x q hb ((hJ _).except (hK _)) hx
    have hV:= hz.up (show (2:ℝ)^12*H^2/LX^6*(B'+A)≤ _ from mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ)^12≤2^13 by norm_num) (sq_nonneg _)) (by positivity)) (add_nonneg hB hv))
    exact (he.plus hV).likewise (fun w=> Filter.EventuallyEq.of_eq (add_sub_cancel ..))
end Tour
end YM.Trace.Perfect
