import YM.TraceExtension.Perfect.Zinnia

/-! # heading P and Q in finite tensor spans -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free Asymptotics
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side}
local notation "V"=> TypeFace 1
variable (S:StepData c f)(W:CrossA S.ratio.count)(x:Site f)
-- coefficient monomials actual position w
private def paintK {A:TypeFace 1→Body 1 c→ℝ} (b:Loc G 1) (i:Lines G c 1):= if i.2.2=b.2 then A b.1 (i.1,i.2.1) else 0
def ore (b:Loc G 1) (p : Axis):pairA G c→ℝ:=Sum.elim (paintK (A:=fun u=> Perfect.move (cab S.ratio W x u) p 0) b) 0
def nug (b:Loc G 1)(i j:Axis):pairA G c→ℝ:= Sum.elim (paintK (A:=fun u=> Perfect.move (Perfect.move (cab S.ratio W x u) i) j 0) b) 0
def fed (b:Loc G 1): pairA G c→ℝ:= Sum.elim (fun _=>0) (paintK (A:=fun u=> Perfect.trench S x (0,u)) b)

private lemma icon_zero (s:Lines G c 1)(v:Lines G f 1): palest 0 v s= 0:=by
 rcases s with ⟨i,x,y⟩;rcases v with ⟨t,j,k⟩; rw [palest, show uniformM _ _ _=_ from gate_f 0 (t,j) k (i,x) y]; simp

lemma as_pen (u: Lines G f 1)(z:pairA G c): amber S W x (Sum.inl u) z = ∑ a:Axis, RowGrade.price (.foot a) (lift (u.1-x))*ore S W x u.2 a z:=by
 rcases u with ⟨i,v,b⟩; cases z with
 | inr z=> simp only [ore,Sum.elim_inr,Pi.zero_apply,mul_zero,sum_const_zero];rfl
 | inl z=>
    obtain ⟨p,y,d⟩:= z; unfold amber doubling palest; dsimp only [Sum.elim_inl]
    rw [show uniformM _ _ _=_ from gate_f _ (i,v) b (p,y) d]; split <;> rename_i h
    · change lin _ _ _=_; simp only [lin,Finset.sum_apply,Pi.smul_apply,ore,paintK, h, ↓reduceIte,Sum.elim_inl]; rfl
    simp [ore,paintK,h]
lemma amber_cal (u:Lines G f 1): ∀ z:pairA G c, amber S W x (.inr u) z=0:=by rintro (z|z);rfl; exact icon_zero _ _
lemma as_dan (u : Lines G f 1)(z:pairA G c): aquifer S W x (.inl u) z=∑ a:Axis,∑ b:Axis, quadT a b (lift (u.1-x))* nug S W x u.2 a b z:=by
 rcases u with ⟨v,l,x₀⟩; cases z with
 | inl z=> rcases z with ⟨i,j,b⟩; unfold aquifer doubling palest; dsimp only [Sum.elim_inl];rw [show uniformM _ _ _=_ from gate_f _ (v,l) x₀ (i,j) b]; split <;> rename_i h
           · change ((quad _ _) _)= _; simp only [quad,Finset.sum_apply,nug,paintK,Pi.smul_apply,h, ↓reduceIte,Sum.elim_inl]; rfl
           simp [nug,paintK,h]
 | inr z=>simp [aquifer,doubling,nug]
lemma aquas (u : Lines G f 1)(z:pairA G c): aquifer S W x (.inr u) z=fed S x u.2 z:=by
 rcases u with ⟨v,p,j⟩; cases z
 · rfl
 next z=> rcases z with ⟨q,i,w⟩; unfold aquifer doubling fed paintK; dsimp only [Sum.elim_inr]; unfold palest; rw [show uniformM _ _ _ = _ from gate_f _ (v,p) j (q,i) w]; rfl

-- payment from SETTLE, bound second coefficients via samples polynomial finite torus; `nug` double derivative cross symmetric
lemma nug_tie (b : Loc G 1)(i j:Axis): nug S W x b i j=nug S W x b j i:=by
 ext1 z; unfold nug paintK; simp_rw [move_swap (x:=0) (i:=i) (j:=j)]

lemma lifted_test (v:Cover)(a:Axis)(i:Axis): RowGrade.price (.foot a) v=(v a:ℝ):=rfl

-- P row salary from steps
lemma orbitC (h:11≤ f.val)(p:Axis)(u:Loc G 1): amber S W x (.inl (x+step p,u))= ore S W x u p:=by
 have he : lift ((x+step p)-x)=step p:=by
    rw [add_comm x, add_sub_cancel_right]; apply lift_eq_iff.mpr ⟨by simp, fun i=>?_⟩; by_cases H:i=p <;> simp [H] <;> omega
 ext1 i; rw [as_pen]; dsimp only; rw [he,sum_eq_single p]
 · simp [RowGrade.price]
 · intro j _ hk; simp [RowGrade.price,hk]
 simp
-- Q on diag: 2step -> exactly nug. Q off: step+step -> canonical kernel.
lemma mineC (h:11 ≤ f.val)(p q:Axis)(u:Loc G 1): aquifer S W x (.inl (x+ step p +step q,u))= nug S W x u p q:=by
 have hZ: lift ((x+step p+step q)-x)=step p+step q:=by
    apply lift_eq_iff.mpr ⟨by simp only [map_add,wrap_step]; abel, fun i=> ?_⟩; by_cases ht:i=p <;> by_cases hv:i=q <;> simp [*,Ne.symm] <;> omega
 funext i; rw [as_dan]; dsimp only; rw [hZ]; by_cases hh:q=p
 · subst q; rw [sum_eq_single p,sum_eq_single p];rotate_left
   · intro j _ h; simp [quadT,h,Ne.symm h]
   · simp
   · intro j _ h; apply Finset.sum_eq_zero; intro k _; by_cases he: j=k <;> first| (subst k; simp [h,quadT])|simp [he,h,quadT]
   · simp
   norm_num [quadT]
 have hp (j:Axis)(hj:j≠p)(hh':j≠q): ∑ a, quadT j a (step p+step q) * nug S W x u j a i=0:= by
    apply sum_eq_zero; intro a _; simp [quadT,hj,hh']
 rw [← add_sum_erase _ _ (Finset.mem_univ p), sum_eq_single (s:=univ.erase p) q]; rotate_left
 · intro b hb ht; exact hp b (mem_erase.mp hb|>.1) ht
 · simp [hh]
 rw [sum_eq_single (s:=univ) q,sum_eq_single (s:=univ) p]; rotate_left
 · intro b _ h; by_cases hb:b=q <;> simp [quadT, h,hh,hb, eq_comm] <;> simp [Ne.symm hb]
 · simp
 · intro b _ he; by_cases hb:b=p <;> simp [quadT,hh,he,hb, Ne.symm hh, eq_comm] <;> simp [Ne.symm hb]
 · simp
 rw [nug_tie S W x u q p]; simp [quadT,Ne.symm hh, hh]; ring
end YM.Trace.Perfect
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free Asymptotics RowGrade
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge}(S:StepData c f)(W:CrossA S.ratio.count)(x:Site f)

abbrev Ore (G:Gauge):= Loc G 1× Axis
abbrev Bar (G:Gauge):= (Loc G 1×Axis×Axis) ⊕ Loc G 1
def meshOre (x:Ore G)(o:Site f): Acr G f:= ballad (.foot x.2,x.1) o
def meshBar (x:Bar G)(o:Site f): Acr G f:= x.elim (fun p=> Sum.elim (fun v:Lines G f 1=> if v.2=p.1 then quadT p.2.1 p.2.2 (lift (v.1-o)) else 0) 0) (fun v=> ballad (.watch,v) o)
def carnel (x':Ore G):= ore S W x x'.1 x'.2
def lagoon (x':Bar G): pairA G c→ℝ:= x'.elim (fun v=>nug S W x v.1 v.2.1 v.2.2) (fed S x)
lemma surface (i:pairA G c): (fun j=> amber S W x j i)=∑ v:Ore G, carnel S W x v i • meshOre v x:=by
 ext1 j; rw [Finset.sum_apply]; unfold carnel meshOre; cases j
 next j=> rw [as_pen,Fintype.sum_prod_type,Finset.sum_eq_single j.2]; rotate_left
          · intro a _ h; apply Finset.sum_eq_zero; intro _ _; simp [ballad,strollT,Ne.symm h]
          · simp
          apply Finset.sum_congr rfl; intro i _; simp [ballad,strollT,mul_comm]
 next j=> rw [amber_cal]; simp [ballad]
lemma waters (i:pairA G c): (fun j=> aquifer S W x j i)=∑ v:Bar G, lagoon S W x v i • meshBar v x:=by
 ext1 j; rw [Finset.sum_apply,Fintype.sum_sum_type]; unfold lagoon meshBar; cases j
 next j=> rw [as_dan,Fintype.sum_prod_type, Finset.sum_eq_single j.2]; rotate_left
          · intro a _ h; apply Finset.sum_eq_zero; intro _ _; simp [ballad, Ne.symm h]
          · simp
          rw [Fintype.sum_prod_type]; simp [ballad]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro v _; exact mul_comm ..
 next j=> rw [aquas]; simp [ballad,strollT,mul_ite,price]
lemma economize {L C α:ℝ}{V:pairA G f→ pairA G c → ℝ}{R:pairA G c →ℕ}{t:ℕ}(hz:0≤α) (h:Settle R (landW x) V (amber S W x) (aquifer S W x) α t L C)(hF:11≤f.val)(hp:1 ≤ L) (hc:0≤C):
    (∀ i, sh R α t 0 (carnel S W x i) ≤ 2*C) ∧ (∀ i,sh R α t 0 (lagoon S W x i) ≤ 9*C):=by
 constructor
 · rintro ⟨b,i⟩; unfold carnel; rw [← orbitC S W x hF]; let k : pairA G f:=Sum.inl (x+step i,b); refine (h.p k).trans ?_
   have hv: (landW x k:ℝ) ≤ 1:=by
       change (separation x (x+step i):ℝ) ≤ _; rw [separation_comm,separation,add_comm x,add_sub_cancel_right]; exact_mod_cast pdist_step (n:=f) i
   rw [mul_comm 2]; apply mul_le_mul_of_nonneg_left _ hc; apply le_trans (div_le_self (by positivity) (one_le_pow₀ hp));linarith
 rintro (⟨v,u,z⟩|v)
 · unfold lagoon; simp only [Sum.elim_inl]; rw [← mineC S W x hF]; let k : pairA G f:=Sum.inl (x+step u+step z,v); refine (h.q k).trans ?_
   have hv: (landW x k:ℝ) ≤ 2:=by
       have hz(j:Site f)(i:Axis): separation j (j+step i) ≤ 1:=by rw [separation_comm,separation,add_comm j,add_sub_cancel_right]; exact pdist_step _
       exact_mod_cast ((separation_triangle x (x+step u) (x+step u+step z)).trans (Nat.add_le_add (hz x u) (hz (x+step u) z)))
   rw [mul_comm 9]; apply mul_le_mul_of_nonneg_left _ hc; apply le_trans (div_le_self (by positivity) (one_le_pow₀ hp)); nlinarith [Nat.cast_nonneg (α:=ℝ) (landW x k)]
 unfold lagoon; simp only [Sum.elim_inr]; rw [← show aquifer S W x (.inr (x,v))=fed S x v from funext (aquas S W x (x,v))]; refine (h.q _).trans ?_
 simp only [landW, separation_self,Nat.cast_zero,add_zero,one_pow]; rw [mul_comm 9]; apply mul_le_mul_of_nonneg_left _ hc; exact (div_le_self zero_le_one (one_le_pow₀ hp)).trans (by norm_num)

lemma slotAg (a b:Axis)(x:Cover) : quadT a b x=((paw a b).price x - 1/4*(paw a a).price x- 1/4*(paw b b).price x)/4 -(if a=b then (1/2:ℝ) else 0) * (foot a).price x:=by unfold quadT; unfold price; dsimp only; split <;> ring
-- need independent λ
lemma prism_foot (v : Loc G 1)(a b : Axis)(x:Site f):
    meshBar (Sum.inl (v,a,b)) x= (1/4:ℝ) • (ballad (paw a b,v) x - (1/4:ℝ) • ballad (paw a a,v) x - (1/4:ℝ) • ballad (paw b b,v) x) - (if a=b then (1/2:ℝ) else 0) • ballad (foot a,v) x:=by
 ext1 i; cases i
 next i=>
    simp only [meshBar,ballad,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]; by_cases H:i.2=v <;> simp [slotAg,H,strollT] <;> ring
 next i=> split <;> simp [ballad,meshBar]
end YM.Trace.Perfect
