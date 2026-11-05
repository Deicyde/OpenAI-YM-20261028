import YM.Contacts.Score.Arcs
/-!
# Joint election with any finite/infinite-shell alternatives registered

Distributional formula algebra. Aims for integral of this joint form (with all test and
norm qualifications proved later), not an expansion into products of distributions at a point.
Allows projection of these forests as well, each branch estimated according to the requirements
at its own vertex and test data. The linear projections at successive vertices are allowed to be
different because the tags weld a whole word at the next stage.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered MultipleContact MultipleContact.Script
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {k : ℕ} {A : Type} {E F : Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
namespace System
variable {g : Group k} (P : E→ₗᵢ[ℝ] Points k) (s : ℝ) (T : System E (Grammar A) k)
variable (f : Menu k) (Q : Pieces g)(i : Q.parts)
local notation "Z!" => Grammar A
local notation "D" => Board (Group k) A

def election := System.forest (fun j=> T.vote P s j (f j)) Q
def present (j : Group k) := retag E (tag j) (T.vote P s j (f j))
def back := Ordered.product (Q.parts.erase i.val) (T.present P s f)
def attend (X : Score E Z!) := T.back P s f Q i * retag E (tag i.val) X
def absentee (X : E→ Z! →ₗ[ℂ] Z!) := T.attend P s f Q i (reshape X (T.punctured P s i.val))
lemma order : permitted (T.present P s f) := fun a b h=> Mark.agree (Mark.relabel (T.focused P s a (f a)) _) (Mark.relabel (T.focused P s b (f b)) _) fun _ _ h' h''=> h'.ready h'' (normals_distinct P h)
lemma split_election : T.election P s f Q = T.attend P s f Q i (T.vote P s i.val (f i.val)) := split_last _ i.property (T.present P s f) ((T.order P s f).stands Q)
lemma standard (h : ∀ i∈ Q.parts,f i=Ballot.whole) : T.election P s f Q = T.coupled P s Q := by unfold election coupled forest parcel; apply eq_product; intro i hi; simp only [h i hi,T.all_votes] -- rw [h i hi,T.all_votes]
lemma varied (b:Ballot) : T.election P s (Function.update f i.val b) Q=T.attend P s f Q i (T.vote P s i.val b):= by
   rw [T.split_election P s _ Q i,Function.update_self,attend,attend,back,back]; apply congrArg (· * _); apply eq_product; intro j hj; simp [present,Function.update_of_ne (Finset.mem_erase.mp hj).1]
lemma renew (h : 1 < i.val.card) : T.election P s f Q= ∑ v∈T.slate i.val (f i.val), T.attend P s f Q i (T.candidate P s i.val v (f i.val)) := by
   rw [T.split_election P s f Q i,T.pays P s i.val (f i.val) h,attend,map_sum, Finset.mul_sum]; rfl
lemma camp (x : E)(a : SmoothTests E)(b : Ballot)(v : T.Arm i.val) : action x a (T.attend P s f Q i (T.candidate P s i.val v b)) = action x
      (sliceAt P i.val b.slice (T.maskAt P s i.val v a)) (T.absentee P s f Q i (T.treatment i.val v)):= by
   rw [absentee,attend,candidate,maskScore,attend,← takeRight, ← takeRight]; simp_rw [map_mul,retag_rules,mul_assoc]
lemma renewal (h : 1 < i.val.card)(x : E)(a : SmoothTests E): action x a (T.election P s f Q)=
    ∑ v∈T.slate i.val (f i.val), action x (sliceAt P i.val (f i.val).slice (T.maskAt P s i.val v a)) (T.absentee P s f Q i (T.treatment i.val v)) := by rw [T.renew P s f Q i h,map_sum]; simp_rw [T.camp]
lemma shape (U : Splittings i.val) (F : E→ Z!→ₗ[ℂ] Z!) : T.attend P s f Q i (reshape F (parcel (T.full P s) U.val))=
   reshape (fun x=>review Q i U.val (F x)) (T.election P s (widenMenu U f) (replace i U.val)):= by
    let X:= widenMenu U f; let t := T.present P s X; let l:=Q.parts.erase i.val; let r:=U.val.parts; let y:= T.present P s f; let J:= Ordered.product r (fun i=> retag E (tag i) (T.full P s i)); let k':= T.back P s f Q i
    have hh : T.election P s X (replace i U.val) = k'*J:= by
        change product (replace i U.val).parts t = product l y* J; have he:=(T.order P s X).stands (replace i U.val); rw [replace_parts] at he ⊢; rw [union_commutes (replace_disj i U.val) t he]; congr 1
        · exact eq_product (fun j hj=> congrArg (fun b:Ballot=> retag E (tag j) (T.vote P s j b)) (menu_unchanged U f (Finset.disjoint_left.mp (replace_disj i U.val) hj)))
        exact eq_product fun j hj=> by simp_rw [t,present,X,menu_small U f hj,T.all_votes]
    have hx:= fork_without (r:Set (Group k)) l (Finset.disjoint_coe.mpr (replace_disj i U.val)) (fun j=> T.vote P s j (f j)); have hv:= fork_inside (r:Set (Group k)) r (by rfl) (T.full P s)
    have ht:= rebuild_left (r:Set (Group k)) k' J (fun (x:E)=> (tag i.val).toLinearMap.comp (F x)) hx hv
    rw [hh, attend, retags,reshape_composes]; exact ht.symm
lemma onPatch (U : Splittings i.val) (hx : plane i.val ≤ LinearMap.range P.toLinearMap)(a : SmoothTests E)(he : tsupport a.val ⊆ bright P U.val)(X : E→ Z!→ₗ[ℂ] Z!) :
   T.absentee P s f Q i X * instructionScore E D (mask a) = reshape (fun x=>review Q i U.val (X x)) (T.election P s (widenMenu U f) (replace i U.val)) * instructionScore E D (mask a) := by
     rw [← T.shape P s f Q i U X]; unfold absentee attend; simp_rw [mul_assoc,← retag_rules (tag (A:=A) i.val) (mask a),← map_mul,← reshape_instruction]; rw [departure P _ _ _ _ hx a (Q.nonempty_of_mem_parts i.property) U.property (fun x hx=> bright_slots (he hx))]
lemma in_splitting (U : Splittings i.val) (hx : plane i.val ≤ LinearMap.range P.toLinearMap)(a : SmoothTests E)(he : tsupport a.val ⊆ bright P U.val)(X : E→ Z!→ₗ[ℂ] Z!)(x:E) :
   action x a (T.absentee P s f Q i X) = review Q i U.val (X x) (action x a (T.election P s (widenMenu U f) (replace i U.val))) := by rw [← action_reshape (fun x=> review Q i U.val (X x))]; exact replace_test a x (T.onPatch P s f Q i U hx a he X)

local notation "𝒫" => Pieces i.val
variable (F' : Menu k)
lemma wax (R : 𝒫) (u v:R.parts) (F : E→ Grammar A→ₗ[ℂ] Grammar A): Mark (Adhesive (detector P u.val v.val))
      (T.attend P s F' Q i (reshape F (parcel (T.cumulant P s) R))):= by
    let d:= detector P u.val v.val; apply Mark.prod (R:= Adhesive d) (T:=Adhesive d) (S:=Adhesive d) ?_ ?_ (fun _ _ ha hb=> ha.multiply hb)
    · apply Adhesive.fixed; exact ((T.order P s F').stands Q).mono (Finset.coe_subset.mpr (Finset.erase_subset ..))
      intro q h; obtain ⟨hh,hq⟩:= Finset.mem_erase.mp h; have he : Disjoint q i.val := Q.disjoint hq i.property hh; exact ((T.focused P s q (F' q)).relabel (tag q)).switch (fun l ht=> Attention.adhesive ht (in_detector P (.inr (Disjoint.mono_right (R.le u.property) he)) (.inr (Disjoint.mono_right (R.le v.property) he))))
    refine Mark.relabel (Mark.transformed (Adhesive.fixed R.parts (T.cumulant P s) ((T.compatible P s).stands R) ?_) _) _
    intro q hq; have hh(a:R.parts) : q=a.val ∨ Disjoint q a.val:= (Or.elim (Classical.em (q=a.val)) Or.inl fun he=>Or.inr (R.disjoint hq a.property he)); exact (T.translatesOrigin P s q).switch (fun l hl=> Adhesive.of_track hl (in_detector P (hh u) (hh v)))

lemma precursorE (Y : E→ Grammar A→ₗ[ℂ] Grammar A) : T.absentee P s F' Q i Y=
     ∑ R∈(Finset.univ.erase (⊤:Pieces i.val)), T.attend P s F' Q i (reshape Y (parcel (T.cumulant P s) R)):= by
   unfold absentee attend punctured receding; rw [map_sum,map_sum,Finset.mul_sum]
variable (hp : plane i.val ≤ LinearMap.range P.toLinearMap)
include hp
lemma announces [MeasureSpace E][BorelSpace E][(volume: Measure E).IsAddHaarMeasure] {I : Type*}(Y : E→ Grammar A→ₗ[ℂ] Grammar A) {f : I → SmoothTests E} {a : SmoothTests E} {φ: Filter I} (h : ∀ x:E,(normalOn P i.val).starProjection x≠0→∀ᶠ t in φ,(f t).val =ᶠ[𝓝 x] a.val) :
     ∀ᵐ x:E,∀ᶠ t in φ, action x (f t) (T.absentee P s F' Q i Y)= action x a (T.absentee P s F' Q i Y) := by
   let p : Finset (Pieces i.val):= Finset.univ.erase ⊤; let n(R : Pieces i.val):= T.attend P s F' Q i (reshape Y (parcel (T.cumulant P s) R))
   have ht (R) (hr:R∈ p) : ∀ᵐ x:E,∀ᶠ t in φ, action x (f t) (n R)= action x a (n R):= by
      obtain ⟨u,hu,v,hv,he⟩:= many (show R≠ ⊤ from (Finset.mem_erase.mp hr).1) (Q.nonempty_of_mem_parts i.property)
      have hU:=R.nonempty_of_mem_parts hu; have hV:=R.nonempty_of_mem_parts hv; let d:= detector P u v
      filter_upwards [ae_unequal hU hV (R.disjoint hu hv he) (R.subset hu) (R.subset hv) hp] with x hx
      refine Adhesive.reads (wax P s T Q i F' R ⟨u,hu⟩ ⟨v,hv⟩ Y) (fun x hD=> h x ?_) (fun H=> hx (sub_eq_zero.mp H))
      intro hh; have he : Collapsed i.val (P x):= (local_collapse hp x).mpr hh
      apply hD; apply sub_eq_zero.mpr; exact (centroid_same hU _ _ (fun a ha=> he _ (R.le hu ha))).trans ((centroid_same hV _ _ (fun a ha=> he _ (R.le hv ha))).symm)
   filter_upwards [(eventually_all_finset p).mpr ht] with x hx; filter_upwards [(eventually_all_finset p).mpr hx] with t ht; rw [precursorE, map_sum,map_sum]; exact Finset.sum_congr rfl ht
end System
end YM.Contacts.Normal
