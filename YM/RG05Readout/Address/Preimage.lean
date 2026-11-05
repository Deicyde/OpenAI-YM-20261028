import YM.RG05Readout.Address.Mobile
/-!
# Fiber summations on the actual aligned path

Partial mark and later density aggregation. The engineering restoration is
*not* another power per stencil location. Here all relative weights in 3+1,
once for that slot with nonperiodic address convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
section math
variable {A E:Type*}[Fintype A][Nonempty A]
variable [AddCommGroup E][Module ℂ E]

def average (f:A→E):E:=(Fintype.card A:ℂ)⁻¹ • ∑ i,f i
lemma ave_single (e:E):average (fun _:A=>e)=e:=by
   have h:(Fintype.card A:ℂ) ≠ 0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
   rw [average,Finset.sum_const,Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,inv_mul_cancel₀ h,one_smul]
omit [Nonempty A] in
lemma ave_add (f g:A→E): average (f+g)= average f+average g:=by simp only [average,Pi.add_apply,Finset.sum_add_distrib,smul_add]
omit [Nonempty A] in
lemma ave_smul (f:A→E) (z:ℂ):average (z • f)=z • average f:=by simp only [average,Pi.smul_apply,← Finset.smul_sum,smul_comm _ z]
-- aggregate costs
variable {G:Gauge}{C:Family G}{d:ℕ}
lemma ave_size (f:A→Palette C d) {t:ℝ}(h:∀ i,size (f i) ≤ t): size (average f) ≤ t:=by
   rw [average,size_smul, norm_inv, Complex.norm_natCast]; have hr : 0 < (Fintype.card A:ℝ):= Nat.cast_pos.mpr Fintype.card_pos
   apply le_trans (mul_le_mul_of_nonneg_left ((size_sum ..).trans (Finset.sum_le_sum (fun i _=> h i))) (inv_pos.mpr hr).le)
   rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
omit [Nonempty A] in
lemma slide_product (f:Palette C d)(w:A→Mark C d→E):average (fun i=> Slide f (w i))= Slide f (fun j=> average (fun i=>w i j)):=by
   unfold Slide average; rw [Finset.sum_comm,Finset.smul_sum]; apply Finset.sum_congr rfl (fun i _=> ?_); rw [← Finset.smul_sum,smul_comm]
end math

variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ c t:ℝ} (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "δ"=> displacement C p m
local notation "L"=> C.path.S.block m
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))} (hw: Plot D s K c α β T)
variable (u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1:Signed) (child C p m i))
-- ONE at origin. Later this relation costs on replicated polynomial per mark w/o multiplicativity assumption.
def orient (f:Tape G (C.side (m+1) p))(i: O):Tape G (C.side (m+1) p):=(shiftTape (ψ i) (u i)).comp f

inductive Train (P:Tape G (C.side (m+1) p))(Q:Tape G (C.side m p))(x:ℝ): Prop where
 | route (f:O→Tape G (C.side m p))(h:∀ i,Travel C N m p d (ψ i) D ((orient u P i).comp (Native.pull (δ i) ℓ)) (f i) x)(hq: Q=average f):Train P Q x

variable (h:C.Makes)(hm:m<N)
section deck
variable {D u}{P Q:Tape G (C.side (m+1) p)}{V H:Tape G (C.side m p)} {x w:ℝ}
lemma Train.easier (hP:Train (d:=d) D u P V x)(hp:x≤ w):Train (d:=d) D u P V w:= by obtain ⟨f,h,rfl⟩:=hP; exact ⟨f,fun i=>(h i).extend hp,rfl⟩
include hm h
lemma Train.join (hD:SoundDoor Z D)(hP:Train (d:=d) D u P V x)(hQ:Train (d:=d) D u Q H w): Train (d:=d) D u (P+Q) (V+H) (x+w):=by
   obtain ⟨f,hF,rfl⟩:=hP; obtain ⟨g,hG,rfl⟩:=hQ; refine ⟨f+g,fun i=> ?_, (ave_add f g).symm⟩
   rw [orient,LinearMap.comp_add,LinearMap.add_comp]; exact (hF i).add (hG i) h hm hD
omit hm h in
lemma Train.gain (z:ℂ)(hP:Train (d:=d) D u P V x):Train (d:=d) D u (z • P) (z • V) (‖z‖*x):=by
   obtain ⟨f,hF,rfl⟩:=hP; refine ⟨z • f, fun i=>?_,(ave_smul f z).symm⟩
   rw [orient,LinearMap.comp_smul,LinearMap.smul_comp]; exact (hF i).smul z
lemma Train.lots {A:Type*}{P:A→Tape G (C.side (m+1) p)}{V:A→Tape G (C.side m p)}{x:A→ℝ}(I:Finset A)(hD:SoundDoor Z D)(hP:∀ i∈ I,Train (d:=d) D u (P i) (V i) (x i)):Train (d:=d) D u (∑ i∈I,P i) (∑ i∈I,V i) (∑ i∈I,x i):=by
   induction I using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; refine ⟨0,?_,?_⟩; intro i; unfold orient; simp only [LinearMap.comp_zero, LinearMap.zero_comp]; exact Travel.vac le_rfl; simp [average]
   | @insert i I hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact Train.join h hm hD (hP i (Finset.mem_insert_self ..)) (ih (fun j hj=> hP j (Finset.mem_insert_of_mem hj)))
end deck

-- approximate averaged heading (not literal calibration)
structure South (l:Mark C d→Palette C d):Prop where
   paid (i:Mark C d) : size (l i) ≤ margin d c K*chargeN L i
   grants i : size (Address.clear C d (weights i) (l i-leadScale C L i (T i.1))) ≤ oldCost d K*α
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "∂"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K

inductive Made (w:Mark C d→Palette C d)(P:Tape G (C.side (m+1) p))(x:Palette C d)(r:ℝ)(Q:Tape G (C.side m p))(z:Palette C d): Prop where
   | turn (f:Palette C d)(h: Printed C d R 0 (Kc m) Q f z (Ω*size (amplify d C L x)+η'*r)) (hr: Train (d:=d) D u P Q (tollP d K c β*size (amplify d C L x)+∂*r)) (hx:size (f-Slide x w) ≤ η'*r): Made w P x r Q z

include h hw hm u
lemma yield_now : ∃ l:Mark C d→Palette C d, South (C:=C) (m:=m) (c:=c) (K:=K) (α:=α) (T:=T) l ∧ ∀ (V:Tape G (C.side (m+1) p)) (x y:Palette C d) (t:ℝ), Printed C d M 0 (Kc (m+1)) V x y t → ∃ U z, Made (d:=d) (c:=c) (K:=K) (α:=α) (β:=β) D u l V x t U z:=by
   choose f X Y hF using fun i:Bud C p m=>slip h hm (ψ i) (Bud.personal C p m i) hw (dist_box C p m i); let g (j:Mark C d):= average (fun i=> X i j)
   refine ⟨g,⟨fun j=> ave_size _ (fun i=> (hF i).age j),fun j=>?_⟩,fun V x y t hV=>?_⟩
   · let r:=weights j; let Q:=leadScale C L j (T j.1); let P i:=Address.clear C d r (X i j-Q);
     suffices ht: Address.clear C d r (g j-Q)=average P by rw [show _-leadScale _ _ _ _=g j-Q from rfl,show weights j=r from rfl, ht]; exact ave_size _ (fun i=>(hF i).debits _)
     rw [show g j-Q=average (fun i=> X i j-Q) from ?_]; unfold average; rw [map_smul,map_sum];
     change g j-Q=average ((fun i=> X i j)+(fun _:O=>-Q)); rw [ave_add,ave_single,←sub_eq_add_neg]
   have he(i:Bud C p m):∃ V':Tape G (C.side m p),∃ l z:Palette C d,Course (D:=D) (ψ i) ((orient u V i).comp (Native.pull (δ i) ℓ)) V' l z (Ω*size (amplify d C L x)+ η'*t) (tollP d K c β*size (amplify d C L x)+∂*t) ∧ size (l-Slide x (X i)) ≤ η'*t:=by
       let H:= (shiftTape (ψ i) (u i)).comp V; obtain ⟨l,hP⟩:=moveprint (ψ i) (u i) V x y ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) h hV
       rw [mul_assoc (decay ..),mul_assoc (tollV ..)] -- factors
       exact stitch h hm (ψ i) (Bud.personal C p m i) hw (dist_box C p m i) H x l _ hP (hF i)
   choose V' l z hL hz using he
   have ha:Printed C d R 0 (Kc m) (average V') (average l) (average z) (Ω*size (amplify d C L x)+η'*t):=by
       have hi:=hw.cursor.sense d le_rfl
       let e:= (Fintype.card O:ℂ)⁻¹; have h0:= (Printed.all (Real.sqrt_pos.mpr (forcedPos C.path.levels m)) (h.wilson.represents N p m hm.le).good Finset.univ hi.order hi.power (fun i _=>(hL i).paid)).twist hi.order hi.power e
       apply h0.grow; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,norm_inv, Complex.norm_natCast,← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne_zero), one_mul]
   refine ⟨_,_,Made.turn (average l) ha ⟨V',fun i=> (hL i).ready,rfl⟩ ?_⟩
   rw [← slide_product]; rw [sub_eq_add_neg, ← show average (- (fun i=> Slide x (X i)))= - average (fun i=> Slide x (X i)) from ?_,← ave_add]
   · apply ave_size; simpa [sub_eq_add_neg] using hz -- wrong
   unfold average; simp
end YM.RG05Readout.Address
