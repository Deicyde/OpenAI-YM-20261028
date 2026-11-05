import YM.Next.STATIONARY.FrameEst.PatchGeometry
import YM.Next.STATIONARY.FrameEst.Stencils




set_option autoImplicit false
/-!
# Canonical packing and actual static mean/range. Integer offsets
honored. Independent of pre/post. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Tree
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f}
variable (S)

abbrev unitSplit (G : Gauge) (S : StepData c f) (i : ℕ) := splitCo S.ratio (Loc G i)
abbrev ParcelG (G : Gauge) (L : Side) := Co L (Loc G 1) ⊕ (Loc G 0)

def drawerC (α β : Type) (c : Side) : Co c α ⊕ (Co c β) ≃ Co c (α⊕β) := (Equiv.prodSumDistrib ..).symm

def clothe (G : Gauge) (S : StepData c f) : Bodies G c f ≃ Co c (ParcelG G S.patch.L) :=
    (Equiv.sumCongr (unitSplit G S 1) (Equiv.refl (Lines G c 0))).trans (drawerC ..)
lemma inflowL (x : Lines G f 1) : clothe G S (.inl x) = ((unitSplit G S 1 x).1,Sum.inl (unitSplit G S 1 x).2) := rfl


-- derivatives

def curryG (G : Gauge) (S : StepData c f) : Matrix (Lines G c 0) (Lines G f 0) ℝ := LinearMap.toMatrix' (LinearMap.pi fun a : Lines G c 0 =>
    ∑ i : S.patch.Points, S.patch.weight i • (LinearMap.proj (Precision.atPoint S a.1 i,a.2) : BaseSites G f→ₗ[ℝ] ℝ))
def bondsM (G : Gauge) (S : StepData c f) := patron G (Precision.mean S)
lemma curry_at (x : BaseSites G f) (a) : (curryG G S*ᵥ x) a=∑ i : S.patch.Points,S.patch.weight i*x (Precision.atPoint S a.1 i,a.2) := by
  rw [curryG, LinearMap.toMatrix'_mulVec]; simp
lemma bonds_spot (x : Link G f) (a : Lines G c 1) : (bondsM G S*ᵥ x) a= ∑ i:S.patch.Points,S.patch.weight i* ∑ j : Fin S.patch.L.val, x (Precision.atPoint S a.1 i + j.val • step (axisEquiv.symm a.2.1),a.2) := by
  let k := parts G 1 (arm G f 1 x) a.2.2
  let m := axisEquiv.symm a.2.1
  have hh n (y : Site _) : integralLink y (List.replicate n (posDir m)) k=∑ i : Fin n, x (y+i.val • step m,a.2) := by
    change linkSum _ _ _= _
    induction n generalizing y with
    | zero => simp [linkSum]
    | succ i IH =>
      rw [List.replicate_succ, Fin.sum_univ_succ,linkSum,IH];
      simp only [Step.vec,Step.used,Bool.false_eq_true,↓reduceIte,posDir]
      rw [Fin.val_zero,zero_smul,add_zero]
      congr 1
      · rw [show coord m=_ from axisEquiv.apply_symm_apply a.2.1]; rfl
      apply sum_congr rfl; intro j _; rw [Fin.val_succ, add_smul,one_smul, ← add_assoc, add_right_comm]
  rw [bondsM,patron_fee]
  change (Precision.mean S*ᵥ k) (a.1,a.2.1)=_
  rw [Precision.mean,LinearMap.toMatrix'_mulVec]; simp only [LinearMap.pi_apply,LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [show S.repath (axisEquiv.symm a.2.1)=List.replicate _ _ from rfl]; exact sum_congr rfl fun i _ => by rw [show integralLink _ _ k = _ from hh _ _]; rfl

lemma jar_boat (v : Phase (Lines G f 0)) (a) : (approached (curryG G S)*ᵥ v) a=∑ i : S.patch.Points,(S.patch.weight i:ℂ)*v (Precision.atPoint S a.1 i,a.2) := by
  refine Leads.buys (p:=fun x => (approached (curryG G S) *ᵥ x) a) (q:=fun x : Phase (Lines G f 0) => ∑ i : S.patch.Points,(S.patch.weight i:ℂ)*x (Precision.atPoint S a.1 i,a.2)) (fun u v => ?_) (fun u v => ?_) ?_ v
  · exact congr_fun ((Leads.byVec (curryG G S)) u v) _
  · simp only [Pi.add_apply,Pi.smul_apply, smul_eq_mul,Finset.mul_sum,mul_add,Finset.sum_add_distrib]; simp only [mul_left_comm _ I]
  intro i; rw [prom_vec]; simp [axes,curry_at]
lemma bonds_boat (v : Phase (Lines G f 1)) (a) : (approached (bondsM G S)*ᵥ v) a=∑ i : S.patch.Points,(S.patch.weight i:ℂ)* ∑ j : Fin S.patch.L.val, v (Precision.atPoint S a.1 i + j.val • step (axisEquiv.symm a.2.1),a.2) := by
  refine Leads.buys (p:=fun x => (approached (bondsM G S) *ᵥ x) a) (q:=fun v => ∑ i : S.patch.Points,(S.patch.weight i:ℂ)*∑ j : Fin S.patch.L.val,v (Precision.atPoint S a.1 i + j.val • step (axisEquiv.symm a.2.1),a.2)) (fun u v => ?_) (fun u v => ?_) ?_ v
  · exact congr_fun ((Leads.byVec (bondsM G S)) u v) _
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul, Finset.sum_add_distrib,Finset.mul_sum, mul_add];
    simp only [Finset.sum_add_distrib,mul_left_comm _ I]
  intro i; rw [prom_vec]; simp [axes,bonds_spot]

section importers
variable {F B : Type} [Fintype F] [Fintype B] [DecidableEq F] [DecidableEq B]

lemma import_in (U : Matrix (Co c F) (Co f B) ℂ) (p : Site c) (v : Phase (Co S.patch.L B)) :
    U*ᵥ poured S.ratio p v = repackM (Equiv.refl _) (splitCo S.ratio B) U *ᵥ tune p v := by
  have hx := repack_act (Equiv.refl _) (splitCo S.ratio B) U (poured S.ratio p v)
  rw [show poured S.ratio p v ∘ (splitCo S.ratio B).symm=tune p v by ext1 i; simp [poured]; rfl] at hx; exact hx.symm
end importers

lemma bond_travel : Jaunt (repackM (Equiv.refl (Lines G c 1)) (unitSplit G S 1) (approached (bondsM G S))) (meanRay G S.patch) 0 := by
  intro p q h v; rw [← import_in S,add_zero]; ext1 a; rw [bonds_boat]
  let d := axisEquiv.symm a.2.1
  have he i (j : Fin S.patch.L.val) : Precision.atPoint S a.1 i+j.val • step d=wrap f (i.val+j.val • step d)+S.ratio.embed a.1 := by rw [Precision.atPoint, map_add,map_nsmul,wrap_step, add_right_comm]
  change ∑ i:S.patch.Points,(S.patch.weight i:ℂ)*∑ j : Fin S.patch.L.val, poured S.ratio p v (Precision.atPoint S a.1 i+j.val • step d,a.2) = cell p a.1 *((∑ j : Fin S.patch.L.val, _)*ᵥ v) a.2
  simp_rw [he]; simp only [scrap_pour S.ratio p a.1 q h, Matrix.sum_mulVec, Finset.sum_apply,coast_earn, Finset.mul_sum]
  rw [sum_comm]; apply sum_congr rfl; intro j _; refine Eq.trans ?_ (congr_arg (cell p a.1 * ·) (coast_earn S.patch (fun a : Loc G 1 => axisEquiv.symm a.1) j.val q (v:Phase (Co S.patch.L (Loc G 1))) a.2).symm); rw [ Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [mul_left_comm]; rfl
lemma jar_travel : Jaunt (repackM (Equiv.refl (Lines G c 0)) (unitSplit G S 0) (approached (curryG G S))) (jar G S.patch) 0 := by
  intro p q h v; rw [← import_in S,add_zero]; ext1 a; rw [jar_boat]; change _=cell p a.1*(jar _ _ q*ᵥ v) a.2
  simp only [Precision.atPoint, scrap_pour S.ratio p a.1 q h, jar,coast_earn, zero_smul, add_zero, Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [mul_left_comm]; rfl
end YM.Stationary
end

/-!
# Two physical roles at c. Counting arms from ANY Ratio. Canonical real basis
mapping. Payload formula for vertical precision.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Tree
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {G : Gauge} {P : Patch} {c f k L : Side} {S : StepData c f} {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {p : Site c} {q : Momentum}



section joins
variable (R : Type) [CommRing R] (α β c)

def shardX : Matrix α (α ⊕ β) R := LinearMap.toMatrix' (LinearMap.pi fun i : α => LinearMap.proj (.inl i : α ⊕ β))
def shardY : Matrix β (α ⊕ β) R := LinearMap.toMatrix' (LinearMap.pi fun i : β => LinearMap.proj (.inr i : α ⊕ β))
variable (x : α ⊕ β→R)
lemma sliceX : shardX α β R *ᵥ x=x ∘ Sum.inl := by rw [shardX,LinearMap.toMatrix'_mulVec]; rfl
lemma sliceY : shardY α β R *ᵥ x=x ∘ Sum.inr := by rw [shardY,LinearMap.toMatrix'_mulVec]; rfl
lemma shardPromX : approached (shardX α β ℝ)=shardX α β ℂ := by ext i (j|j) <;> simp [shardX,LinearMap.toMatrix'_apply,approached,Pi.single_apply] <;> split <;> simp_all
lemma shardPromY : approached (shardY α β ℝ)=shardY α β ℂ := by ext i (j|j) <;> simp [shardY,LinearMap.toMatrix'_apply,approached,Pi.single_apply] <;> split <;> simp_all
end joins

variable (G c f)

def butt := rearM G c f
def brim := billsM (helmets G c f) (pocket _) (ContinuousLinearMap.snd ℝ (Link G f) (BaseSites G c))

lemma helmet_ear (u : Vault G c f) : cash (helmets G c f) u=Sum.elim u.1 u.2 := by funext i; rcases i with i|i; exact (cash_prod_left ..).trans (congr_fun (cash_pocket _) _); exact (cash_prod_right ..).trans (congr_fun (cash_pocket _) _)
lemma helmet_butt : butt G c f= shardX (Lines G f 1) (Lines G c 0) ℝ := by
  apply bill_eq (helmets G c f); intro x; rw [butt,rear_cost, sliceX,helmet_ear]; rfl
lemma helmet_brim : brim G c f= shardY (Lines G f 1) (Lines G c 0) ℝ := by apply bill_eq (helmets G c f); intro x; rw [brim,bill_at,cash_pocket,sliceY,helmet_ear]; rfl
variable {G c f}
lemma butt_travel : Jaunt (repackM (unitSplit G S 1) (clothe G S) (approached (butt G c f))) (fun _ => shardX (Co S.patch.L (Loc G 1)) (Loc G 0) ℂ) 0 := by
  classical
  intro i p _ v; let B := unitSplit G S 1; let T := clothe G S
  let w := tune i v ∘ T
  rw [add_zero,show tune i v=w ∘ T.symm by ext1 a; simp [w,T]]
  rw [helmet_butt,shardPromX,repack_act _ (clothe G S) _ w, sliceX]
  refine Eq.trans ?_ (congr_arg (tune i) (sliceX (Co S.patch.L (Loc G 1)) (Loc G 0) ℂ v).symm)
  funext a; obtain ⟨b,rfl⟩ := B.surjective a; simp only [Function.comp_apply,w]; rw [show (unitSplit G S 1).symm (B b)=b from B.symm_apply_apply b,inflowL]; rfl
lemma brim_travel : Jaunt (repackM (Equiv.refl _) (clothe G S) (approached (brim G c f))) (fun _ => shardY (Co S.patch.L (Loc G 1)) (Loc G 0) ℂ) 0 := by
  classical
  intro i p _ v; let T := clothe G S; let w := tune i v ∘ T
  rw [add_zero,show tune i v=w ∘ T.symm by funext j; simp [w]]
  rw [helmet_brim,shardPromY, repack_act _ (clothe G S) _ w, sliceY,sliceY]; funext a; rfl

lemma serial_butt (X : Slab α) (Y : Slab β) : serial X (X.spade Y) q q (shardX α β ℂ) 1 := by
  refine Slab.serial_of zero_le_one fun i => ?_
  rw [sliceX,one_mul];
  have he := Slab.spade_rate (p:=q) (u:=i∘Sum.inl) (v:=i∘Sum.inr) X Y; rw [← spade_assemble] at he
  have hp (j : Phase (α⊕β)) : 0 ≤ (X.spade Y).rate q j := slug_nonneg _
  nlinarith [hp i,sq_nonneg (Y.rate q (i∘Sum.inr))]
lemma serial_brim (X : Slab α) (Y : Slab β) : serial Y (X.spade Y) q q (shardY α β ℂ) 1 := by
  refine Slab.serial_of zero_le_one fun i => ?_
  rw [sliceY,one_mul]
  have he := Slab.spade_rate (p:=q) (u:=i∘Sum.inl) (v:=i∘Sum.inr) X Y; rw [← spade_assemble] at he
  have hp (j : Phase (α⊕β)) : 0 ≤ (X.spade Y).rate q j := slug_nonneg _
  nlinarith [hp i,sq_nonneg (X.rate q (i∘Sum.inl))]

-- actual gauge column in centered basis as z=u at f; sign convention u brings A down

variable (S)
def spreadM := (butt G c f)ᵀ * mail (1:Config G f) - (brim G c f)ᵀ * curryG G S
lemma parliament (V : BaseSites G f) : spreadM (G:=G) S *ᵥ V = cash (helmets G c f) (-gradientA G f V, -(curryG G S*ᵥ V)) := by
  rw [spreadM,sub_mulVec,← Matrix.mulVec_mulVec V (butt G c f)ᵀ, ← Matrix.mulVec_mulVec V (brim G c f)ᵀ,mailed,cant_one,helmet_ear]
  funext i
  cases i <;> simp [-Matrix.mulVec_mulVec, helmet_brim,helmet_butt,shardX,shardY,Matrix.mulVec,dotProduct, Pi.single_apply,ite_mul]
end YM.Stationary
end

/-!
# Bang linear choreography, packed on one coarse cell. Register for
independent apertures/tilts on ANY given patch. Derivatives use bill seats
in this packing. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {c f : Side} {G : Gauge} {P : Patch} {K : KernelChoices}

abbrev Acts (G : Gauge) (P : Patch) := (Loc G 1)⊕ ((ParcelG G P.L)⊕((ParcelG G P.L)⊕(Loc G 1)))

section pack
variable (G) (S : StepData c f)

abbrev WarpV := Corn (Co c (ParcelG G S.patch.L))
def directX (S : StepData c f) : Vault G c f ≃L[ℝ] WarpV G S := LinearEquiv.toContinuousLinearEquiv <|
    (cash (helmets G c f)).trans (LinearEquiv.funCongrLeft ℝ ℝ ((clothe G S).symm))
lemma direct_pay (x : Vault G c f) : directX G S x=cash (helmets _ _ _) x ∘ (clothe G S).symm := rfl
-- folded global in Acts. Build arg pair with nested sum

def wiredFrame {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (c : Side) : (Corn (Co c A) × Corn (Co c B))≃L[ℝ] Corn (Co c (A⊕B)) := LinearEquiv.toContinuousLinearEquiv {
  toFun a i := Sum.elim (fun j => a.1 (i.1,j)) (fun j => a.2 (i.1,j)) i.2
  invFun v := (fun i => v (i.1, .inl i.2), fun i => v (i.1, .inr i.2))
  map_add' a b := funext fun i => by cases i with | mk i j => cases j <;> rfl
  map_smul' a b := funext fun i => by cases i with | mk i j => cases j <;> rfl
  left_inv v := rfl
  right_inv v := funext fun i => by rcases i with ⟨i,j|j⟩ <;> rfl }

def pavilionB : Bang G c f ≃L[ℝ] Corn (Co c (Acts G S.patch)) := by
    classical
    exact (ContinuousLinearEquiv.prodAssoc ℝ (Link G c) (Vault G c f) (Vault G c f × Link G c)).trans
      (((ContinuousLinearEquiv.refl ℝ (Link G c)).prodCongr (((directX G S).prodCongr (((directX G S).prodCongr (ContinuousLinearEquiv.refl ℝ (Link G c))).trans (wiredFrame c))).trans (wiredFrame c))).trans (wiredFrame c))
-- index assignments

def footVoice (P : Patch) (v : Bool) (i : ParcelG G P.L) : Acts G P := if v then .inr (.inr (.inl i)) else .inr (.inl i)
def highVoice (P : Patch) (v : Bool) (i : Loc G 1) : Acts G P := if v then .inr (.inr (.inr i)) else .inl i
-- scalar support
def hymn (P : Patch) (i : Piano G P) : Acts G P := match i with
    | .inl (v,a,j) => footVoice G P v (.inl (wrap P.L a.val,j))
    | .inr (.inl (v,_,b)) => footVoice G P v (.inr (vac,b))
    | .inr (.inr (v,i)) => highVoice G P v i

def carol (P : Patch) (i : Piano G P) : Cover := match i with
    | .inl (_,a,_) => rent P.L a.val
    | .inr (.inl (_,some a,_)) => step a
    | _ => 0

variable {G}
lemma pavilionB_high (x : Bang G c f) (v : Bool) (i : Lines G c 1) :
    pavilionB G S x (i.1,highVoice G S.patch v i.2) = if v then x.2.2 i else x.1.1 i := by cases v <;> rfl
lemma pavilionB_low (x : Bang G c f) (v : Bool) (i : Site c) (j) :
    pavilionB G S x (i,footVoice G S.patch v j) = directX G S (if v then x.2.1 else x.1.2) (i,j) := by cases v <;> rfl
lemma direct_in (x : Vault G c f) (i : Bodies G c f) : directX G S x (clothe G S i)=Sum.elim x.1 x.2 i := by rw [direct_pay,Function.comp_apply,Equiv.symm_apply_apply,helmet_ear]
lemma sewn (z : Cover) (i : Site c) : wrap f z+S.ratio.embed i=S.ratio.assemble (wrap c (rent S.patch.L z)+i,wrap S.patch.L z) := by
  have hx : S.ratio.embed (wrap c (rent S.patch.L z)+i)=S.ratio.embed (wrap c (rent S.patch.L z))+S.ratio.embed i := map_add S.ratio.root ..
  rw [Ratio.assemble,hx,S.ratio.embed_wrap]
  conv_lhs => rw [rent_balance S.patch.L z, map_add];
  unfold StepData.ratio; abel
lemma direct_low (x : Vault G c f) (z : Cover) (i) (j) : directX G S x (wrap c (rent S.patch.L z)+i,.inl (wrap S.patch.L z,j))=x.1 (wrap f z+S.ratio.embed i,j) := by
  rw [sewn]; let Y := wrap c (rent S.patch.L z)+i; let P := wrap S.patch.L z
  rw [show ((Y, .inl (P,j)) : Co c (ParcelG G S.patch.L))=clothe G S (.inl (S.ratio.assemble (Y,P),j)) by
    rw [inflowL,unitSplit,split_co, S.ratio.assemble_parent,S.ratio.assemble_res]; rfl,direct_in]; rfl
lemma direct_high (x : Vault G c f) (i) (j) : directX G S x (i,.inr j)=x.2 (i,j) := direct_in S x (.inr (i,j))
lemma pavilionB_here (x : Bang G c f) (i) (j) : pianist S i x j=pavilionB G S x (wrap c (carol G S.patch j)+i,hymn G S.patch j) := by
  rcases j with ⟨v,a,j⟩| (⟨v,a,j⟩| ⟨v,j⟩)
  · simp only [carol,hymn,pavilionB_low,direct_low]; cases v <;> rfl
  · cases a with
    | none => simp only [carol,hymn,map_zero,zero_add,pavilionB_low,direct_high]; cases v <;> rfl
    | some b => simp only [carol,hymn,wrap_step,pavilionB_low,direct_high]; rw [add_comm]; cases v <;> rfl
  simp only [carol,hymn,map_zero,zero_add]
  change pianist S i x _=pavilionB _ _ _ (_, highVoice G S.patch v j); rw [show pavilionB G S x (i,highVoice G S.patch v j)= _ from pavilionB_high S x v (i,j)]; cases v <;> rfl
end pack
end YM.Stationary
end

/-!
# Evaluation of complex beats of stencil scores from actual patch phase hands.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {c f : Side} {α β : Type} [Fintype α] [Fintype β] {G : Gauge} {P : Patch} {K : KernelChoices} {A : Audience α} {C D κ : ℝ} {n m t : ℕ}
-- install DecidableEq to avoid search brittle
instance (G : Gauge) (P : Patch) : DecidableEq (Piano G P) := Classical.typeDecidableEq _
instance (G : Gauge) (P : Patch) : DecidableEq (Acts G P) := Classical.typeDecidableEq _

section ext
variable [DecidableEq β] {R : Corn β→ℕ→Prop} {u : Fin n → Phase β} {b : Fin n→ℕ} {M : α → Corn β→ℝ}
def Shiny (R : Corn β→ℕ→Prop) (x : Phase β) (k : ℕ) : Prop := R (fun i => (x i).re) k ∧ R (fun i => (x i).im) k
lemma through_charge (h : Tested A R M n C) (hp : ∀ i, Shiny R (u i) (b i)) (hv : (∑ i,b i) ≤ 2) : Hearing A (∑ i,b i) (fun i => beat (M i) 0 n u) ((2:ℝ)^n*C) := by
  classical
  let f i (p : Bool) : Corn β := if p then fun j => (u i j).im else fun j => (u i j).re
  let q (i : Bool) := if i then Complex.I else 1
  have hf i (a : Bool) : R (f i a) (b i) := by cases a; exact (hp i).1; exact (hp i).2
  have hx : (fun i => ∑ a : Bool,q a • axes (f i a))=u := by
    funext i j; simp [axes,Finset.sum_apply,q,f]; rw [add_comm,mul_comm Complex.I,Complex.re_add_im]
  have he (x : α) : beat (M x) 0 n u = ∑ v : Fin n→Bool,(∏ i,q (v i))*beat (M x) 0 n (axes ∘ fun i => f i (v i)) := by
    conv_lhs => rw [← hx]
    rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun v _ => MultilinearMap.map_smul_univ (beat (M x) 0 n) (fun i => q (v i)) _
  simp_rw [he]; rw [show (2:ℝ)^n*C=∑ _ : Fin n→ Bool,C by simp]
  have hu i : ‖q i‖=1 := by cases i <;> simp [q]
  refine Hearing.join _ (fun v _ => ?_)
  exact (h (fun i => f i (v i)) b (fun i => hf i (v i)) hv).softer (fun x => by rw [beat_real]; simp [norm_prod,hu])
end ext

-- `melody` bulletin filtered. Input scalar points from arbitrary Momentum.
def imprintsC (G : Gauge) (P : Patch) (q : Momentum) : Phase (Acts G P) →ₗ[ℂ] Phase (Piano G P) :=
    LinearMap.pi fun i => mode q (carol G P i) • (LinearMap.proj (hymn G P i))
lemma imprints_read (x : Phase (Acts G P)) (p : Momentum) (i) : imprintsC G P p x i=mode p (carol G P i)*x (hymn G P i) := rfl
lemma flips_melody (x : Phase (Acts G P)) {p q} (hp : rolls p q) : imprintsC G P p x=imprintsC G P q x := by ext1 i; rw [imprints_read,imprints_read,hp.exp]
@[fun_prop] lemma melody_diff {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {v : X→ Phase (Acts G P)} {p : X→Momentum} {x} (hx : DifferentiableAt ℂ v x) (hp : DifferentiableAt ℂ p x) :
    DifferentiableAt ℂ (fun z => imprintsC G P (p z) (v z)) x := by
  apply differentiableAt_pi.mpr; intro i; simp only [imprints_read]
  exact (((show Differentiable ℂ (fun p : Momentum => mode p (carol G P i)) by unfold mode; fun_prop).differentiableAt.comp x hp).mul (differentiableAt_pi.mp hx _))

section bills
variable (S : StepData c f)

def rehearsal (i : Site c) : Corn (Co c (Acts G S.patch))→L[ℝ] BassInput G S.patch := pianist S i ∘L ((pavilionB G S).symm : _ →L[ℝ] Bang G c f)
def applause (G : Gauge) (S : StepData c f) (i : Site c) : Phase (Co c (Acts G S.patch)) →ₗ[ℂ] Phase (Piano G S.patch) := LinearMap.pi (fun j : Piano G S.patch => LinearMap.proj (wrap c (carol G S.patch j)+i,hymn G S.patch j))
lemma applause_fits (x : Corn (Co c (Acts G S.patch))) (i : Site c) : axes (rehearsal S i x) = applause G S i (axes x) := by
  ext1 j; unfold rehearsal axes; simp only [ContinuousLinearMap.comp_apply]; change ((pianist S i ((pavilionB G S).symm x) j : ℝ):ℂ)=_; rw [show pianist S i ((pavilionB G S).symm x) j= _ from pavilionB_here S ..,(pavilionB G S).apply_symm_apply]; rfl
lemma audience_act (p : Site c) {q} (h : rolls (mon p) q) (v : Phase (Acts G S.patch)) (i : Site c) :
    applause G S i (tune p v)=cell p i • imprintsC G S.patch q v := by
  ext1 j; simp [imprints_read,applause,tune,cell_wrap,h.exp]; ring
lemma audition (p : Fin n→ Site c) (q : Fin n→ Momentum) (he : ∀ i,rolls (mon (p i)) (q i)) (v : Fin n→Phase (Acts G S.patch)) (i) (M : BassInput G S.patch→ℝ) (h : AnalyticAt ℝ M 0) :
    beat (M ∘ rehearsal S i) 0 n (fun j => tune (p j) (v j))=cell (∑ j,p j) i * beat M 0 n (fun j => imprintsC G S.patch (q j) (v j)) := by
  rw [evaluated _ (fun v => applause_fits S v i) h, MultilinearMap.compLinearMap_apply]; simp only [audience_act S _ (he _),MultilinearMap.map_smul_univ,cell_hom]; rfl
end bills
end YM.Stationary
end

/-!
# Palette test for linear temporal profiles. No singular weight divisions
for Hess legs. Reach: σ≤1. Costs from packing BEFORE L.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α : Type} [Fintype α] {L : Side} {K : KernelChoices} {A : Audience α} {G : Gauge} {P : Patch} {C D σ : ℝ} {m n : ℕ}

-- venue pockets direction condition

def pawn (v : Bool) (x : Phase (Acts G P)) : Phase (Co P.L (Loc G 1)) := x ∘ footVoice G P v ∘ Sum.inl
def signet (v : Bool) (x : Phase (Acts G P)) : Phase (Loc G 1) := x ∘ highVoice G P v
def capitals (v : Bool) (x : Phase (Acts G P)) : Phase (Loc G 0) := x ∘ footVoice G P v ∘ Sum.inr
def roster (z : Phase (Co L α)) (b : Site L) : EuclideanSpace ℂ α := WithLp.toLp 2 (stackSlice b z)

structure Veil (C : ℝ) (x : Phase (Acts G P)) (k : ℕ) : Prop where
  grade : k≤1
  fine v : Hearing (balcony (Site P.L)) k (roster (pawn v x)) (inch P.L*C)
  skins v : slug (capitals v x)≤C
  bonds v : slug (signet v x)≤C

section tours

def entryRoom (j : ℕ) := 4+4*(j+5)
def visitor (j : ℕ) : Finset Cover := box (entryRoom j)
def admission (j : ℕ) := (Fintype.card ↥(visitor j):ℝ)
def muralRoom (j : ℕ) := Real.exp (entryRoom j) * admission j
instance (j : ℕ) : Nonempty ↥(visitor j) := ⟨⟨0, center_box _⟩⟩
lemma admit_pos (j : ℕ) : 1 ≤ admission j := by
  unfold admission; exact_mod_cast Fintype.card_pos (α:=↥(visitor j))
lemma muralRoom_pos (j : ℕ) : Real.exp 1 ≤ muralRoom j :=
   (Real.exp_monotone (show (1:ℝ) ≤ ↑(entryRoom j) by exact_mod_cast (show 1≤entryRoom j from by unfold entryRoom; omega))).trans (le_mul_of_one_le_right (by positivity) (admit_pos j))
lemma mural_one (j : ℕ) : 1≤muralRoom j := (Real.one_le_exp (by norm_num)).trans (muralRoom_pos j)
lemma park_scap (a : Plaza P) : Laurent.size (rent P.L a.val)≤entryRoom P.J := by
  exact_mod_cast (show (Laurent.size (rent P.L a.val):ℝ) ≤ ↑(entryRoom P.J) by simpa only [entryRoom,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using rent_pay P a.val a.property)
def mural_obey (a : Plaza P) : ↥(visitor P.J) × Site P.L := (⟨rent P.L a.val,by
    let k := rent P.L a.val
    have he i : (k i).natAbs≤entryRoom P.J := le_trans (single_le_sum (s:=univ) (f:=fun i:Axis => (k i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)) (park_scap a)
    apply box_test.mpr; constructor <;> intro i <;> set x:=k i <;> have hv : x.natAbs ≤ entryRoom P.J := he i
    · change _ ≤ k i; omega
    change k i ≤ _; omega⟩,wrap P.L a.val)
lemma mural_inj (P : Patch) : Injective (mural_obey (P:=P)) := by
  intro i j h; have ht : rent P.L i.val=rent P.L j.val := congr_arg (fun v => (v : ↥(visitor P.J) × _).1.val) h
  have hv : wrap P.L i.val=wrap P.L j.val := congr_arg Prod.snd h
  apply Subtype.ext; rw [rent_balance P.L i.val]; rw [ht,hv, ← rent_balance]
lemma mural_ports (i : Plaza P) : (balcony (Plaza P)).weight i ≤ admission P.J * (balcony _).weight (mural_obey i) := by
  have h : Fintype.card P.Points ≤ Fintype.card (Plaza P) := Fintype.card_le_of_injective (fun i => (⟨i.val,alley i⟩ : Plaza P)) (fun a b h => Subtype.ext (congr_arg (fun i : Plaza P => i.val) h))
  have hp : (P.L.val:ℝ)^4 ≤ Fintype.card (Plaza P) := (alley_pin P).trans (by exact_mod_cast h)
  have hi : 0 < (P.L.val:ℝ)^4 := by positivity
  have ht : 0 < (Fintype.card ↥(visitor P.J):ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [balcony,admission,Fintype.card_prod,Lattice.site_card]; push_cast
  field_simp
  exact hp
lemma mode_voice (a : Plaza P) {p : Momentum} (h : p∈strip (1:ℝ)) : ‖mode p (rent P.L a.val)‖≤Real.exp (entryRoom P.J) :=
    (reward _ _ 1 (fun i => (h i).le)).trans (Real.exp_monotone (by rw [one_mul]; exact_mod_cast park_scap a))
lemma venue_step (i : Option Axis) {p : Momentum} (h : p∈strip (1:ℝ)) : ‖mode p ((i.map (fun i => step i)).getD 0)‖≤Real.exp 1 := by
  apply (reward _ _ (1:ℝ) (fun i => (h i).le)).trans; rw [one_mul]; apply Real.exp_monotone
  cases i with
  | none => simp
  | some i => simp [Laurent.size,apply_ite Int.natAbs]
lemma carried_shine {p : Momentum} (h : p∈strip (1:ℝ)) (u : Phase (Co P.L α)) (hp : Hearing (balcony (Site P.L)) n (roster u) C) : Hearing (balcony (Plaza P)) n (fun a => WithLp.toLp 2 (fun i => scrap p u a.val i)) (muralRoom P.J*C) := by
  let F := fun i : ↥(visitor P.J) × Site P.L => roster u i.2
  have he : Hearing (balcony _) n F C := by rw [← balcony_circus]; exact hp.on_right
  have hx : Hearing (balcony (Plaza P)) n (F ∘ mural_obey) (admission P.J*C) := Hearing.crops (g:=_) univ (mural_obey (P:=P)) (mural_inj P|>.injOn) (admit_pos _) (fun i _ => ⟨le_rfl,mural_ports i⟩) (by simp) he
  rw [muralRoom,mul_assoc]; apply hx.grows (Real.exp _) (by positivity)
  intro i; rw [show (WithLp.toLp 2 (fun j => scrap p u i.val j) : EuclideanSpace ℂ α)=mode p (rent P.L i.val) • F (mural_obey i) from rfl,norm_smul]; exact mul_le_mul_of_nonneg_right (mode_voice i h) (norm_nonneg _)
end tours

lemma thrones (a : G.Color) {ι : Type} [Fintype ι] (f : G.ColorIndex → ι) (h : Injective f) (u : EuclideanSpace ℂ ι) (he : ∀ i, |a i| ≤ ‖u (f i)‖) : ‖a‖≤ ‖u‖ := by
  classical
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]; simp_rw [Real.norm_eq_abs]
  apply (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (he i) 2)).trans
  rw [← Finset.sum_image (f:=fun i => ‖u i‖^2) (by exact h.injOn)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)

lemma shiny_steps (x : Phase (Acts G P)) (hc : Veil C x n) {p : Momentum} (h : p∈strip (1:ℝ)) : Shiny (StaffP G P (muralRoom P.J*C)) (imprintsC G P p x) n := by
  let y := imprintsC G P p x
  have hv (u : ℂ → ℝ) (he : ∀ i, |u i| ≤ ‖i‖) : StaffP G P (muralRoom P.J*C) (u ∘ y) n := by
    refine ⟨hc.grade.trans (by decide),fun b v => ?_,fun b v => ?_,fun b v => ?_⟩
    · rw [mul_left_comm]; refine (carried_shine h (pawn b x) (hc.fine b)).softer (fun i => thrones _ (fun j => (coord v,j)) (fun j k h => congr_arg Prod.snd h) _ (fun j => ?_))
      exact he (mode p (rent P.L i.val)* x (hymn G P (Sum.inl (b,i,(coord v,j)))))
    · let Z := WithLp.toLp 2 (capitals b x)
      let l := mode p ((v.map (fun a => step a)).getD 0)
      have hp : ‖whipC b v (u∘y)‖≤‖l • (Z : EuclideanSpace ℂ (Loc G 0))‖ := thrones _ (fun j => (vac,j)) (fun j k h => congr_arg Prod.snd h) _ (fun j => by
        cases v <;> exact he (y (Sum.inr (Sum.inl (b,_,j)))))
      rw [norm_smul] at hp; exact hp.trans (mul_le_mul ((venue_step v h).trans (muralRoom_pos P.J)) (hc.skins b) (norm_nonneg _) (zero_le_one.trans (mural_one P.J)))
    · have hh : 0≤C := (slug_nonneg _).trans (hc.bonds b)
      apply le_trans (thrones _ (fun j => (coord v,j)) (fun j k h => congr_arg Prod.snd h) (WithLp.toLp 2 (signet b x)) (fun j => ?_)) ((hc.bonds b).trans (le_mul_of_one_le_left hh (mural_one P.J)))
      let i := Sum.inr (α:=Bool × Plaza P × Loc G 1) (Sum.inr (α:=Bool×Option Axis× G.ColorIndex) (b,coord v,j))
      change |u (y i)| ≤ ‖signet b x (coord v,j)‖
      have hx : y i=signet b x (coord v,j) := by unfold y; rw [imprints_read]; simp [i,hymn,signet,carol]
      rw [hx]; exact he _
  exact ⟨hv Complex.re Complex.abs_re_le_norm,hv Complex.im Complex.abs_im_le_norm⟩
end YM.Stationary
end
