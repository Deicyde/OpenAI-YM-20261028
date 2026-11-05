import YM.OPE.Eye.Views
/-!
# Fleeting words on torus & in compression
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U: Final C F S)
variable {I J Z : Type}[Fintype I][Fintype J][Fintype Z] {N p k f b l n : ℕ}
variable {𝓕 : Filter (ℕ×ℕ)}
variable {B:I→ℝ}{D:J→ℝ} {x:I→ Cover} {v:I→ C.book.Token} {y:J→ Cover}{w:J→ C.book.Token}

/-- Used for generic positions before extending to arbitrary separated configurations. -/
def Screen (x:I→ E4):= ∀ i:Axis, Injective fun a=> (x a) i
lemma Screen.coin {x:I→ E4} (h:Screen x) : Injective x:= fun a b h'=>h timeAxis (congr_arg (fun x:E4=> x timeAxis) h') -- lambda implicit?
variable {Q : Schedule}
lemma Screen.lists {x:I→ E4} (h:Screen x) : points (x ∘ runNames I) ∈ generic _ := fun i=> (h i).comp (runNames I).injective
lemma Screen.reserve {x:I→E4}{y:J→E4} : Screen (beside x y) ↔ Screen x ∧ Screen y ∧ ∀ (i:I)(j:J)(a:Axis), x i a≠y j a:=by
    have h a: (Injective fun i=> beside x y i a) ↔ (Injective fun i=> x i a)∧(Injective fun j=>y j a)∧∀ (i:I)(j:J),x i a≠y j a:= by
       have h:= beside_commutes (x:=x) y (fun x:E4=>x a) -- implicit?
       rw [show (fun i=> beside x y i a)=(fun x:E4=>x a) ∘ beside x y from rfl,h]; exact (show Injective (beside (fun i=>x i a) (fun j=>y j a)) ↔ _ from beside_distinct)
    unfold Screen; simp_rw [h]; grind

abbrev ReadLabel (C:Family G) {I : Type} (y:I→ C.book.Token) := (i:I) → ℕ×ℕ → C.label (y i).1

def frozen (C:Family G)(v : I→ C.book.Token): ReadLabel C v:= fun i _=> (v i).2

def germ {v : I→ C.book.Token} (h: ReadLabel C v) (i:I): Cards.Cylinder C:= fun N p=> C.O N p (h i (N,p)) 0

lemma germ_observe {v:I→ C.book.Token} (h:C.Makes)(q: ReadLabel C v) (x : I→ Cover) (N p k:ℕ) (w: Cover) (V : Config G (C.side N p)) : register C k x (germ q) N p (Lattice.translate (location C.S k N p w) V)= ∏ i,C.O N p (q i (N,p)) (location C.S k N p (x i+w)) V:=by
    change (register C k x (germ q) N p ∘ _) V= _; rw [register_step w]; unfold register; refine Finset.prod_congr rfl fun i _=>?_; simp [comp_apply,germ,C.translation] -- sign?
lemma germ_here (q:ReadLabel C v)(x:I→ Cover)(N p k:ℕ)(V:Config G (C.side N p)) : register C k x (germ q) N p V=∏ i,C.O N p (q i (N,p)) (location C.S k N p (x i)) V:=by
    unfold register; simp [comp_apply,germ,C.translation]

structure TileDoc (U:Final C F S)(k:ℕ)(𝓕:Filter (ℕ×ℕ))(a: U.α.unselected.algebra) (g: Cards.Cylinder C) : Prop where
   okay : ∃ E:Episode C F k, ∃ Y:Moving E, E.cluster U.α.unselected=a ∧ travel E Y 𝓕 ∧ ∀ᶠ i in 𝓕, editorial E Y i.1 i.2=g i.1 i.2

-- Episode maker for arbitrary-indexed monomials, could also cooper pairDiff via subtract without Fintype arithmetic dependent imaging.
local notation "A" => U.α.unselected
local notation "T'" => C.S.gridPoint k
structure Spark (C:Family G)(f:Filter (ℕ×ℕ)) (k:ℕ) where
    Index : Type
    [fin : Fintype Index]
    x : Index→ Cover
    v : Index→ C.book.Token
    q : ReadLabel C v
    limit (i: Index): Tendsto (q i) f (𝓝 (v i).2)
    frames : Screen (C.S.gridPoint k ∘ x)
attribute [instance] Spark.fin
namespace Spark
variable (L:Spark C 𝓕 k)
def glance := viewing U ((T') ∘ L.x) L.v
def cuts : Cards.Cylinder C:= register C k L.x (germ L.q)
end Spark
lemma TileDoc.sparks (m:ℕ) (a:Fin m→ℂ) (p:Fin m→ Spark C 𝓕 k) : TileDoc U k 𝓕 (∑ i,a i • (p i).glance U) (fun N r V=> ∑ i,a i*(p i).cuts N r V):=by
    let e i:= runNames (p i).Index; let v i:=(p i).v ∘ e i
    let E: Episode C F k := { num:=m, factor:=a, image i:=Fintype.card (p i).Index, seats i j:= (p i).x (e i j), gen i:= (p i).frames.lists, weight i j:= (v i j).1, point i j:= (v i j).2,current i j _ _:=(v i j).2,views i j:=⟨by simp,(fun _=> (v i j).2),fun _ _=> tendsto_const_nhds,tendsto_const_nhds⟩ }
    let Z: Moving E:= fun i j=> (p i).q (e i j); refine ⟨E,Z,?_, fun i j=>(p i).limit (e i j),?_⟩
    · unfold Episode.cluster; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Spark.glance viewing; rw [dif_pos ((p i).frames.coin)]; rfl
    filter_upwards with c; funext V; unfold editorial Episode.cuts; dsimp only [edition];
    exact Finset.sum_congr rfl fun i _=>by simp only [Spark.cuts,germ_here,add_zero]; change a i * _ = _; rw [← Equiv.prod_comp (e i)]; rfl -- side?
variable {h: ReadLabel C v} {g: ReadLabel C w}
lemma TileDoc.one (hc:Screen ((T') ∘ x))(hp: ∀ i,Tendsto (h i) 𝓕 (𝓝 (v i).2)) : TileDoc U k 𝓕 (viewing U ((T') ∘ x) v) (register C k x (germ h)):=by
    simpa only [Fin.sum_univ_one,one_smul,one_mul] using! TileDoc.sparks U 1 (fun _=>1) (fun _=> {Index:=I,x:=x,v:=v,q:=h,limit:=hp,frames:=hc})
lemma TileDoc.diff (hc:Screen ((T') ∘ x))(hc':Screen ((T') ∘ y))(hp:∀ i,Tendsto (h i) 𝓕 (𝓝 (v i).2)) (hp':∀ i,Tendsto (g i) 𝓕 (𝓝 (w i).2)) : TileDoc U k 𝓕 (viewing U ((T') ∘ x) v - viewing U ((T') ∘ y) w)
    (register C k x (germ h) - register C k y (germ g)):=by
    let F:Spark C 𝓕 k:= {Index:=I,x:=x,v:=v,q:=h,limit:=hp,frames:=hc}; let L:Spark C 𝓕 k:= {Index:=J,x:=y,v:=w,q:=g,limit:=hp',frames:=hc'}
    have he:= TileDoc.sparks U 2 ![1,-1] ![F,L]; simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one, neg_smul,one_smul,neg_mul,one_mul,← sub_eq_add_neg] at he; exact he

-- combination criterion
lemma TileDoc.global {g h} (u:TileDoc U k 𝓕 g h) {q:ℕ}
    {z: I→ Cylinder C}{w:J→ Cylinder C}(hG:Org.Grill C F)(e:b≤k)[𝓕.NeBot](hr:𝓕 ≤ F.fuse) (hX:Gap C.S k x (2*C.S.a b)) (hh:Gap C.S k y (2*C.S.a l))(hS:GapTo C.S k x y (2*C.S.a b))(hP:Hall C.S b l q f n (Fintype.card I) (Fintype.card J))
    (hU:∀ j, ∀ᶠ i in 𝓕, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) (B j) (z j i.1 i.2))
    (hv:∀ j, ∀ᶠ i in 𝓕, PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (w j i.1 i.2))
    (he: ∀ᶠ i in 𝓕,h i.1 i.2= register C k x z i.1 i.2 * register C k y w i.1 i.2) : ‖g‖≤(∏ x,B x)*(∏ y,D y):=by
    obtain ⟨E,Y,rfl,hY,hi⟩:=u.okay
    obtain ⟨i,hI,hJ⟩:= ((eventually_all.mpr hU).and (eventually_all.mpr hv)).exists
    refine carrying e E Y hr U.room (theme U) U.phase.phase.still (reflective U hG) U.phase.phase.decomposition
       (mul_nonneg (Finset.prod_nonneg fun i _=> (hI i).cost) (Finset.prod_nonneg fun i _=>(hJ i).cost)) hY (fun i=> mixed e i U.room.cutoff hr hX hh hS hP hU hv ?_)
    filter_upwards [he,hi] with i he hi using hi.trans he
end YM.OPE
