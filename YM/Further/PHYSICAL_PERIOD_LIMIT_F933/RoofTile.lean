import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Tracery

/-! # Tee positions and maps across systems and their orbits

Horizontal inputs repeat; symmetries used WITH actual orientations and invariant lifts to break
the projected gradient in the smaller torus. Not assuming periodic matrix evaluated in the same tree basis when forest shifted is different data. Choose ONE constant-tag & highly structured forest (import F05 then to any tag/tree).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Macrame.Lace
open Push.Uniform Precision Function Shingle Lattice Gauge Tree RG Wilson Exterior Filter Finset Set Push
open scoped BigOperators Topology Classical
variable {c C f F : Side} {P : Patch}
  {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {M : ℕ} {G : Gauge}

def project (hC : C.val=c.val*M) (he : 2 ≤ c.val) : Lace h H (M^4) where
  low := normal (by rw [hC]; simp) hC
  high := normal (by rw [H,h,hC]; exact ⟨M,by ac_rfl⟩) (by rw [H,h,hC]; ac_rfl)
  stake x := by
    obtain ⟨x,rfl⟩: ∃ z:Cover, wrap _ z=x := ⟨_,wrap_lift x⟩
    simp only [normal,Ratio.embed_wrap,branch] -- second
  legal := he
  taller := he.trans (by rw [hC]; apply Nat.le_mul_of_pos_right; have := C.property; change 0<C.val at this; rw [hC] at this; exact Nat.pos_of_mul_pos_left this)

variable (hC : C.val=c.val*M) (he : 2 ≤ c.val)
local notation "L" => project (h:=h) (H:=H) hC he

namespace Fitted
variable (V : Lace h H M) {B : Forest V.r} {T : Forest V.R} (s : V.Fitted B T)
-- generic accounting, also true for rotations if chosen; need only limb capsules & up-tag direction
lemma volume {ι κ X : Type} [Fintype ι] [Fintype κ] [Fintype X] {a : κ→ι} (h : Fold a M) : Fold (Prod.map a (id : X → X)) M := by
  rintro ⟨i,x⟩; let A := Prod.map a (id : X → X)
  let u : κ ↪ κ×X := ⟨fun k => (k,x), fun _ _ h=> congr_arg Prod.fst h⟩
  have he : parcel A (i,x)=(parcel a i).map u := by ext ⟨k,x⟩; simp [A,u,eq_comm]
  rw [he,Finset.card_map]; exact h i
lemma trees : Fold s.limb M := by
  intro i
  have he : (parcel s.limb i).card=(parcel V.high.cut i.val.1).card := by
    refine Finset.card_bij (fun k hk => k.val.1) (fun k hk => (posted ..).mpr (congr_arg (fun z:B.Free=>z.val.1) ((posted ..).mp hk))) (fun a ha b hb hh => ?_) fun x hx=> ?_
    · have h : (s.limb a)=s.limb b := ((posted ..).mp ha).trans ((posted ..).mp hb).symm
      exact Subtype.ext (Prod.ext hh (congr_arg (fun i : B.Free=>i.val.2) h))
    have he : (x,i.val.2) ∉ T.trunks := mt (s.pines _).mp (by
      change (_,_) ∉_; rw [(posted ..).mp hx,Prod.eta]; exact i.property)
    let f : T.Free := ⟨(x,i.val.2),he⟩
    have h : f∈parcel s.limb i := (posted ..).mpr (Subtype.ext (Prod.ext ((posted V.high.cut i.val.1 x).mp hx) rfl))
    exact ⟨f,h,rfl⟩
  rw [he]; exact V.high.fold _
lemma tree_keys : Fold (s.track (G:=G)) M := (volume (X:=G.ColorIndex) (trees V s))


end Fitted
open Fitted

-- canonical family of deck lenses. low shift lives in kernel of little projection.
def hub (w : Site C) (hL : 2 ≤ C.val) : Lace H H 1 where
  low := parallel w
  high := parallel ((decreed H).embed w)
  stake i := ((decreed H).root.map_add i w).symm
  legal := hL
  taller := hL

abbrev edge (hC : C.val=c.val*M) (he : 2 ≤ c.val) (w : Site C) : Lace H H 1 :=
    hub w (by rw [hC]; have hm := C.property; change 0 < C.val at hm; rw [hC] at hm; exact he.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hm)))
local notation "E" w => edge (H:=H) hC he w
include hC he
variable (T : Forest (decreed h))
abbrev circuit (T : Forest (decreed h)) : Forest (decreed H) := (L).repeater T
abbrev crown : (L).Fitted T (circuit hC he T) := ⟨fun _ => rfl⟩
local notation "BU" => circuit (H:=H) hC he T
local notation "CB" => crown (H:=H) hC he T

lemma silent {w : Site C} (hw : (L).low.cut w=0) (z : Site F) :
      (L).high.cut ((E w).high.cut z)=(L).high.cut z := by
  let V := L
  change splitter _ (_+_) = _
  rw [map_add]; change _+V.high.cut (V.R.embed w)=_; rw [V.stake,hw]
  rw [← Ratio.root_embed,(decreed h).root.map_zero,add_zero]; rfl

lemma fibers {w : Site C} (hw : (L).low.cut w=0) : (E w).Fitted BU BU := ⟨fun x => (congr_arg T.up (silent hC he hw x)).symm⟩

lemma flange {w : Site C} (hw : (L).low.cut w=0) :
    (CB).bores (G:=G) ∘ (fibers hC he T hw).bores = (CB).bores := by
  funext j
  cases j with
  | inl j =>
    change Sum.inl (((splitter _ (j.1.1+w),j.1.2):Body 1 c),j.2)= Sum.inl ((_,j.1.2),j.2)
    rw [map_add,show (splitter _ w)=_ from hw,add_zero]; rfl
  | inr j =>
    change Sum.inr (((CB).limb ((fibers hC he T hw).limb j.1)),j.2)=Sum.inr ((CB).limb j.1,j.2)
    exact congr_arg (fun x:T.Free=> (Sum.inr (x,j.2):Joint T G)) (Subtype.ext (Prod.ext (silent hC he hw j.1.val.1) rfl))

lemma rim (x y : Key BU G) (hx : (CB).track x=(CB).track y) :
    ∃ w : Site C, ∃ hw : (L).low.cut w=0, (fibers hC he T hw).track x=y := by
  have hz := congr_arg (fun q:Key T G=>q.1.val.1) hx; have hD := congr_arg (fun q:Key T G=>q.1.val.2) hx
  let f' := x.1.val.1; let g' := y.1.val.1
  let w := (decreed H).parent g'-(decreed H).parent f'
  have hw : (L).low.cut w=0 := by
    change splitter _ (_-_)=_; rw [map_sub]
    change (L).low.cut (_)-(L).low.cut _=_; rw [← (L).position, ← (L).position]
    change (L).high.cut f'=(L).high.cut g' at hz; rw [hz,sub_self]
  refine ⟨w,hw,Prod.ext ?_ (congr_arg (fun z:Key T G=>z.2) hx)⟩
  apply Subtype.ext; refine Prod.ext ?_ hD
  have h : (decreed H).residue f'=(decreed H).residue g' := by rw [← (L).room, ← (L).room]; exact congr_arg (fun x => (decreed h).residue x) hz
  have p := (decreed H).unpack_at f'
  have a := (decreed H).unpack_at g'
  let F₀ := (decreed H).root
  change f'+F₀ w=g'; unfold w; rw [map_sub]
  change f'+((decreed H).embed _-(decreed H).embed _)=g'; rw [h] at p; calc
    _ = (decreed H).embed ((decreed H).parent f') + wrap F (lift ((decreed H).residue g')) + ((decreed H).embed _ - (decreed H).embed _):= congr_arg (fun z:Site F=>z + ((decreed H).embed ((decreed H).parent g')-(decreed H).embed ((decreed H).parent f'))) p.symm
    _ = _ := (show (decreed H).embed _ + _ + (_-_) = (decreed H).embed ((decreed H).parent g')+wrap F (lift ((decreed H).residue g')) by abel).trans a

lemma spread : Reserved (address BU G ∘ Sum.inr) (CB).track f.val := by
  constructor
  intro i j he hh
  have h₀ := congr_arg (fun k:Key T G => k.1.val.1) he
  refine (blocks_at_floor (n:=f) (N:=F) (by rw [H,hC,h]; exact ⟨M,by ac_rfl⟩)).apart i.1.val.1 j.1.val.1 ?_ fun hx=> hh ?_
  · exact h₀
  refine Prod.ext ?_ (congr_arg (fun z:Key T G =>z.2) he)
  exact Subtype.ext (Prod.ext hx (congr_arg (fun k : Key T G=>k.1.val.2) he))
end YM.Further.PhysicalPeriodLimitF933.Macrame.Lace
