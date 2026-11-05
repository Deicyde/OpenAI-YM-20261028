import YM.RG08.Tack.Plain
/-!
# Lifts to a larger layout. No promotion of scalar prices here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cairn
open Lattice Laurent Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function Stationary Bloch RG
open scoped BigOperators Classical ContDiff Topology ENNReal
variable {I J:Type}{n:ℕ}{P:Side}{σ τ c p:ℝ}

-- structured inject color; no extra loss on these

def hide (e:I↪J):Market I ↪ Market J:=⟨fun x=>(x.1,e x.2),fun i j h=> Prod.ext (show i.1=j.1 from congrArg (fun z:Market J=>z.1) h) (e.injective (congrArg Prod.snd h))⟩
def many {I J:Type}(e:I↪J)(n:ℕ):Tape n I↪Tape n J:=⟨fun x=>e ∘ x,fun _ _ hx=>funext fun i=>e.injective (congrFun hx i)⟩
def install (u:I↪J)(F:Flake n (Market I)): Flake n (Market J):=Function.extend (many (hide u) n) F 0
lemma install_in (u:I↪J)(F:Flake n (Market I))(x):install u F (many (hide u) n x)=F x:= (many (hide u) _).injective.extend_apply ..
lemma install_out (u:I↪J)(F:Flake n (Market I)){x:Tape n (Market J)}(he:x ∉ Set.range (many (hide u) n)): install u F x =0 :=Function.extend_apply' _ _ _ he
lemma hidden (u:I↪J){x y}: (carpet J).span (hide u x) (hide u y)=(carpet I).span x y:=rfl
lemma housing {u:I↪J}(F:Flake n (Market I)){x:Tape n (Market I)}: mark (carpet J) σ (install u F) (many (hide u) n x)=mark (carpet I) σ F x:=by rw [mark,install_in];unfold mark; rw [show (carpet J).radius (many (hide u) n x)=_ from (carpet I).radius_map (f:=hide u) (fun _ _=>hidden u ) x]
lemma install_wind (u:I↪J){F:Flake n (Market I)}(h:Cohort F): Cohort (install u F):=by
 intro s a
 have he (x:Tape n (Market I)):sway s (many (hide u) n x)=many (hide u) _ (sway s x):=rfl
 by_cases ha:a∈Set.range (many (hide u) n)
 · obtain ⟨b,hb⟩:=ha;rw [←hb,he,install_in,install_in,h]
 rw [install_out,install_out _ _ ha];rintro ⟨x,hx⟩
 apply ha; refine ⟨sway (-s) x,?_⟩
 rw [show many (hide u) n (sway (-s) x)=sway (-s) (many (hide u) n x) from rfl,hx,sway_sway,neg_add_cancel,sway_zero]
lemma install_sym (u:I↪J){F:Flake n (Market I)}(h:Sym F):Sym (install u F):=fun e=>funext fun a=> by
  change install u F (a ∘ ⇑e)=_
  by_cases ha:a∈Set.range (many (hide u) n)
  · obtain ⟨b,rfl⟩:=ha
    rw [show ((many (hide u) n b) ∘ ⇑e)=many (hide u) _ (b ∘ ⇑e) from rfl,install_in,install_in]; exact congrFun (h e) b
  rw [install_out,install_out _ _ ha];rintro ⟨x,hx⟩;exact ha ⟨x ∘ ⇑e.symm, by change many (hide u) n x ∘ ⇑e.symm=_;rw [hx]; ext i:1;simp⟩
lemma install_held (u:I↪J){F:Flake n (Market I)} (h:Held (carpet _) σ p F):Held (carpet _) σ p (install u F):=ensign.mpr (fun i z=>by
  by_cases hz:z∈ Set.range (hide u)
  · obtain ⟨c,rfl⟩:=hz
    rw [← (many (hide u) n).injective.tsum_eq (f:=_) ?_] -- name?
    · convert ensign.mp h i c using 1
      apply tsum_congr;intro b;unfold Forms.row;rw [housing];simp [many] -- hide
    intro b hb
    change _≠0 at hb
    by_contra! H
    rw [Forms.row,mark,install_out _ _ H] at hb
    simp [bill] at hb
  simp_rw [Forms.row]; have he (x:Tape n (Market J))(hx:x i=z): install u F x=0:=install_out _ _ (by rintro ⟨b,rfl⟩; exact hz ⟨b i,hx⟩)
  simp only [mark];have hh(x:Tape n (Market J)): (if x i=z then bill (install u F x) (σ*(carpet J).radius x) else 0)=0:=by split <;> rename_i H <;> simp [* ,bill]
  simp [hh])
 end YM.RG08.Cairn
