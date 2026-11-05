import YM.TraceExtension.Perfect.Plank

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type*}{S:W→ Side}{G:Gauge}{c:Side} {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]{N:ℕ}
-- coordinate retractions
lemma left_output (T:W→ Side)(A:∀ w, Lines G (T w) 1 →ℕ) (f:∀ w,Link G (T w)→ X)(h: Calm A f N) :
    Calm (fun (w:W) i=> Sum.elim (A w) (A w) i) (fun w x=> f w (bite G (T w) x).1) N:=by
 refine h.thin _ (fun w=> Function.Embedding.inl) (fun w=> ContinuousLinearMap.fst ℝ _ _ ∘L (bite G _).toContinuousLinearMap) (fun w j=> ?_) (fun w j hh=> ?_) ?_
 · ext1 i; change desk (I:=pairA G (T w)) (.inl j) (.inl i)= desk j i; by_cases he:i=j <;> simp [desk,Pi.single_apply,he]
 · cases j with
   | inl j => exact (hh ⟨j,rfl⟩).elim
   | inr j=> ext1 i; change desk (I:=pairA G (T w)) (.inr j) (.inl i)=_; simp [desk]
 exact fun _ _=>rfl
lemma stamp_entry {c f:Side}(U:Link G c→Stationary.Joint G c f)(S:StepData c f) (t:S.Choices) (x:Acr G c) (j:Lines G f 1):
    stampA S t U x (.inr j)=∑ i:Lines G c 1, shuttle S t (U (bite G c x).1) (input G c (bite G c x).1) (desk j) i*x (.inr i):=by
    unfold stampA bite
    let p:=bite G c x; let F:=shuttle S t (U p.1) (input _ _ p.1); let A:=billsM (pocket _) (pocket _) F
    change (A.transpose *ᵥ p.2) j= _; apply Finset.sum_congr rfl; intro i _
    have he : F (desk j) i=A i j:=by rw [← bill_pay]; unfold desk; rw [Matrix.mulVec_single_one]; rfl
    exact congr_arg (· * p.2 i) he.symm
namespace Lot
variable {P:Patch}{Y:KernelChoices} {p:Clip}{α D β v:ℝ}(L:W→ Lot G P Y p α D)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1)) (o:∀ w,Site (L w).f)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val)) (t:∀ w,(L w).s.Choices)
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
variable (i:∀ w,Lines G (L w).f 1) (y:∀ w,Site (L w).f)
def pairLoc (j: pairA G c):= j.elim (fun a=> a.1) (fun a=>a.1)
def overLoc (y:∀ w,Site (L w).f)(w)(i:pairA G (L w).c):= Sum.elim (fromV L y w) (fromV L y w) i
include hb hp
omit t in
lemma entire (i:∀ w,Lines G (L w).f 1): Calm (fromV L fun w=>(i w).1) (fun w x=> content (F! w x).1 (i w)) N:=by
 let X' w := ((i w).1,(i w).2.1)
 have he:= tailor_content L K o hb hp X' (N:=N)
 refine (he.mapsF (fun w=> EuclideanSpace.proj (i w).2.2) zero_le_one ?_).near (fun w=>Eventually.of_forall fun x=> edge_parts (content (F! w x).1) (X' w) (i w).2.2)
 intro w x; rw [one_mul]; exact PiLp.norm_apply_le ..
omit hb hp in
private lemma local_z (u v:Site c) {r:ℕ}(h: separation v u ≤ r): lift (u-v) ∈ box r:=by
 rw [separation_comm] at h
 apply box_test.mpr;have ht(i):=(component_le (u-v) i).trans h; constructor<;>intro i<;>specialize ht i<;>omega
lemma touch_tangent : Calm (overLoc L fun w=>(i w).1) (fun w x=> stampA (L w).s (t w) (F! w) x (Sum.inr (i w))) N:=by
 let C:= fun w=> overLoc L (fun w=>(i w).1) w; let b:=railMax P
 let y w:= (i w).1; let A w:= (L w).s.ratio; let V w:= (A w).parent (y w);
 let Z(w):=Finset.univ.filter fun j : Lines G (L w).c 1=> separation ((A w).embed j.1) (y w) ≤ b
 let M:= b+P.L.val
 let T:= (box M) ×ˢ (Finset.univ: Finset (Loc G 1))
 have hZ(w): (Z w).card ≤ T.card:=by
     let R:=fun i:Cover× Loc G 1=> (wrap (L w).c i.1+V w,i.2); refine (card_le_card (s:=Z w) (t:=T.image R) ?_).trans (card_image_le)
     intro i hi; have h0 : (A w).count=P.L:= congr_arg Patch.L (L w).patch
     have ht: separation (V w) i.1 ≤ M:=by
        have he:= Corona.below (A w) (V w) i.1
        have hp : separation ((A w).embed i.1) (y w) ≤ b:= (mem_filter.mp hi).2
        have hv:= (Corona.near (A w) (y w)); have hh := separation_triangle ((A w).embed i.1) (y w) ((A w).embed (V w))
        rw [separation_comm ((A w).embed (V w)),h0] at he; refine (Nat.le_mul_of_pos_left _ P.L.property).trans (he.trans ?_)
        unfold V M at *; rw [h0] at hv; omega
     exact mem_image.mpr ⟨(lift (i.1-V w),i.2),mem_product.mpr ⟨local_z _ _ ht,mem_univ _⟩,Prod.ext (by change wrap _ (lift _)+V w=_; rw [wrap_lift, sub_add_cancel]) rfl⟩
 let F w (j:Lines G (L w).c 1)(x:Acr G (L w).c):=shuttle (L w).s (t w) (F! w (bite G _ x).1) (input _ _ (bite G _ x).1) (desk (i w)) j*x (.inr j)
 have he : Calm C (fun w x=>∑ i∈ Z w,F w i x) N:=by
    refine Calm.finitude Z T.card F ?_ hZ
    let E:=Σ w,↥(Z w); let g(w:E):=w.snd.val; have hg(w:E): separation ((A w.1).embed (g w).1) (y w.1) ≤ b:= (mem_filter.mp w.2.property).2
    have hy:= elements (N:=N) (fun w:E=> L w.1) (fun w=> K w.1) (fun w=>o w.1) hb (fun w=>hp w.1) (fun w=> i w.1) (fun w=> t w.1) g b hg
    -- binder inspect
    apply Calm.abide (ContinuousLinearMap.mul ℝ ℝ) (left_output (fun w:E=>(L w.1).c) _ _ hy) (Calm.pick _ (fun w:E=> Sum.inr (g w) : ∀ w:E,pairA G (L w.1).c) b ?_)
    intro j; change separation (i j.1).1 ((A j.1).embed (g j).1) ≤ b; rw [separation_comm]; exact hg j
 refine he.near (fun w=>?_)
 let f := L w; let J : Acr G f.c→L[ℝ] Link G f.c:= ContinuousLinearMap.fst ℝ _ _ ∘L (bite ..).toContinuousLinearMap
 have ht: Tendsto J (𝓝 0) (𝓝 0):=by simpa using J.continuous.tendsto 0
 have hW (j:Lines G f.c 1) (hp: j ∉ Z w): (fun x=> F w j x)=ᶠ[𝓝 0] 0:=by
    have h : railMax f.s.patch<separation (f.s.ratio.embed j.1) (i w).1:=lt_of_not_ge fun hx=> hp (mem_filter.mpr ⟨mem_univ _, hx.trans_eq (congr_arg railMax (L w).patch)⟩)
    filter_upwards [ht.eventually (rail_far (Y:=F! w) (c:=f.c) (input G f.c) f.size.1 f.price (fresh_thaw (L w).law (W:=K! w) (o w)) (fresh_zero f.law _) (i w) j h (t:=t w))] with x hx; change shuttle (L w).s (t w) (F! w (J x)) (input G (L w).c (J x)) (desk (i w)) j * x (.inr j) = 0; rw [show shuttle (L w).s (t w) (F! w (J x)) (input G (L w).c (J x)) (desk (i w)) j= 0 from hx, zero_mul]
 have hh (j:Lines G f.c 1): ∀ᶠ x:Acr G f.c in 𝓝 0, j ∉ Z w → F w j x=0:=by by_cases hh:j ∈ Z w; simp [hh]; exact (hW j hh).mono (fun x hx _=>hx)
 filter_upwards [eventually_all.mpr hh] with x hx
 change _= stampA (L w).s _ _ _ _; rw [stamp_entry]; exact Finset.sum_subset (subset_univ _) (fun i _ h=>hx i h)
end Lot
end YM.Trace.Perfect
