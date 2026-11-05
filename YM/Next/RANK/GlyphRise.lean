import YM.Next.RANK.Alarm

/-!
# Symmetry preservation of merged genuine records
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable {ζ : V→Site n} {τ t : ℝ}
variable (A : ι→ Lifted G ζ t) (B : κ→ Strike G ζ τ) (X : Siren G n τ)
variable (s : Signed) (x : Site n)

def Zperm (p : Equiv.Perm ι) (q : Equiv.Perm κ) (x : Equiv.Perm (Site n)) := Equiv.sumCongr (Equiv.sumCongr p q) x

private lemma lit {X : ι → Support n} {a : Finset ι} {F : Equiv.Perm ι} (e : Equiv.Perm (Site n)) (h : ∀ i,X (F i)=(X i).image e)
    (hh : Ac.Spark X a) : Ac.Spark X (F.finsetCongr a) := by
  change Ac.Spark X (a.map _)
  refine ⟨hh.1.map, fun x hx y hy=> ?_⟩
  obtain ⟨i,hi,rfl⟩:=mem_map.mp hx; obtain ⟨j,hj,rfl⟩:=mem_map.mp hy
  apply Relation.ReflTransGen.lift (r:= Ac.bonds X a) _ _ _ _ (hh.2 i hi j hj)
  rintro c d ⟨hc,hd,v,hT,hV⟩; refine ⟨mem_map.mpr ⟨c,hc,rfl⟩,mem_map.mpr ⟨d,hd,rfl⟩, e v, ?_,?_⟩
  exacts [(h c).symm ▸ mem_image_of_mem _ hT,(h d).symm ▸ mem_image_of_mem _ hV]

private lemma rights (a : Finset (Branch ι κ n)) (p : Equiv.Perm ι) (q : Equiv.Perm κ) (x : Equiv.Perm (Site n)) :
    ((Zperm p q x).finsetCongr a).toRight = a.toRight.map x.toEmbedding := by ext; simp [Zperm]
private lemma lefty (a : Finset (Branch ι κ n)) (p : Equiv.Perm ι) (q : Equiv.Perm κ) (x : Equiv.Perm (Site n)) :
    ((Zperm p q x).finsetCongr a).toLeft.toLeft = a.toLeft.toLeft.map p.toEmbedding := by ext; simp [Zperm]
lemma lith (p : Equiv.Perm ι) (q : Equiv.Perm κ) (y : Equiv.Perm (Site n)) (he : ∀ i,vol A B X (Zperm p q y i)=(vol A B X i).image y) (hv : ∀ i,(A (p i)).extent=(A i).extent.image y)
    (i : Finset (Branch ι κ n)) (hi : cast A B X i) : cast A B X ((Zperm p q y).finsetCongr i):= by
  unfold cast; rw [lefty,rights]
  refine ⟨lit y he hi.1, hi.2.1.map, fun a ha b hb hh=> ?_⟩
  obtain ⟨a,hx,rfl⟩:=mem_map.mp ha; obtain ⟨b,hS,rfl⟩:=mem_map.mp hb
  change Disjoint (A (p a)).extent (A (p b)).extent
  rw [hv,hv, disjoint_image y.injective]; exact hi.2.2 hx hS fun H=> hh (congr_arg _ H)

private def doc (p : Equiv.Perm ι) (q : Equiv.Perm κ) (y : Equiv.Perm (Site n)) (he : ∀ i,vol A B X (Zperm p q y i)=(vol A B X i).image y) (hv : ∀ i,(A (p i)).extent=(A i).extent.image y) :
    Equiv.Perm (Domino A B X) := by
  refine Equiv.subtypeEquiv (Zperm p q y).finsetCongr (fun i=> ⟨lith A B X p q y he hv i,fun H=> ?_⟩)
  let Z:= Zperm p q y
  have ht:=lith A B X p.symm q.symm y.symm ?_ ?_ (Z.finsetCongr i) H
  · change cast A B X (Z.finsetCongr.symm (Z.finsetCongr i)) at ht; rwa [Equiv.symm_apply_apply] at ht
  · intro i; obtain ⟨i,rfl⟩:= Z.surjective i
    change vol _ _ _ (Z.symm (Z i))= (vol _ _ _ (Zperm p q y i)).image _; rw [show _ = i from Z.symm_apply_apply _,he,Finset.image_image]; simp
  intro i; obtain ⟨i,rfl⟩:= p.surjective i; rw [p.symm_apply_apply,hv,Finset.image_image]; simp

structure liftedMove (i j : Lifted G ζ t) : Prop where
  inventory : j.inventory=swath s x i.inventory
  extent : j.extent= swath s x i.extent
  fuel U : j.amount U=i.amount (pull s x U)

def still (A : ι → Lifted G ζ t) := ∀ s : Signed, ∀ x : Site n,∃ U : Equiv.Perm ι, ∀ i, liftedMove s x (A i) (A (U i))

def Trend := ∀ s : Signed,∀ x : Site n,∃ U : Equiv.Perm κ,∀ i, (B (U i)).extent=swath s x (B i).extent ∧ ∀ u, (B (U i)).occ u=(B i).occ (pull s x u)

def Peace := ∀ s : Signed, ∀ x : Site n,∀ y, X.chamber (affine s x y)=swath s x (X.chamber y) ∧
    ∀ u, X.value (affine s x y) u=X.value y (pull s x u)

private lemma image_of {ι : Type} (p : Equiv.Perm ι) (q : Equiv.Perm (Site n)) (X : ι → Support n) (he : ∀ i,X (p i)=(X i).image q) (i : Finset ι) :
    (i.map p.toEmbedding).biUnion X=(i.biUnion X).image q := by
  classical
  induction i using Finset.induction_on with
  | empty=>simp
  | insert a i haha IH=> simp only [Finset.map_insert,biUnion_insert,IH,Equiv.coe_toEmbedding,he,Finset.image_union]

theorem resumes (M : still A) (W : Trend B) (Y : Peace X): still (teat A B X):= by
  intro s x
  obtain ⟨p,hp⟩:= M s x; obtain ⟨q,hq⟩:= W s x; let y:= sends s x
  let Z:= Zperm p q y
  have hv (i) : vol A B X (Z i)= (vol A B X i).image y := by
    rcases i with (i|i)|i
    · change halo 8 (A (p i)).extent = swath s x (halo 8 (A i).extent); rw [(hp i).extent,swath_iffHalo]
    · exact (hq i).1
    exact (Y s x i).1
  let D:=doc A B X p q y hv (fun i=> (hp i).extent)
  have hx (i) : Settle A B X (D i)=swath s x (Settle A B X i):= image_of Z y _ hv i.val
  have hL (i) : (D i).val.toRight= swath s x i.val.toRight:= by
    rw [show (D i).val= (Zperm p q y).finsetCongr i.val from rfl,rights,map_eq_image]; rfl
  refine ⟨D,fun i=> ⟨hL i,hx i,fun U=>?_⟩⟩
  have ha : quake A B X (D i).val U=quake A B X i.val (pull s x U) := by
    change (∏ j∈ (i.val.map Z.toEmbedding),fuel A B X j U)=_
    rw [Finset.prod_map]; refine prod_congr rfl fun j hj=> ?_; rcases j with (j|j)|j
    · exact (hp j).fuel U
    · exact (hq j).2 U
    exact congr_arg (fun z : ℝ=>Nreal (V:=V) z) ((Y s x j).2 _)
  rw [teat_pay,teat_pay]
  have hU : inside A B X (D i) U ↔ inside A B X i (pull s x U) := by
    have h : (D i).val.toLeft.toLeft.biUnion (fun i=> (A i).inventory)= swath s x (i.val.toLeft.toLeft.biUnion (fun i=> (A i).inventory)) := by
      rw [show (D i).val = Z.finsetCongr i.val from rfl, show ((Z.finsetCongr i.val).toLeft.toLeft)=_ from lefty i.val p q y]; exact image_of p y _ (fun i=> (hp i).inventory) _
    unfold inside; rw [hx,h,hL, ← s_flags s x τ U]
    have heS : ∀ a b : Support n,swath s x a∩swath s x b=swath s x (a∩b):=fun a b=> (image_inter a b y.injective).symm
    rw [heS,show flags t U= _ from (s_flags s x t U).symm,heS]; exact and_congr ((image_injective y.injective).eq_iff) ((image_injective y.injective).eq_iff)
  split_ifs with H h₁ h₂; exacts [ha,False.elim (h₁ (hU.1 H)),False.elim (H (hU.2 h₂)),rfl]
end YM.Next.Rank.Alarm
