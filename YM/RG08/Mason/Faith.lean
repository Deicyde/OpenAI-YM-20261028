import YM.RG08.Ducat.Fence
/-! # Abstract quantitative regime. Include even no-block top patch as dummy, tape roles
 over Here as physical cases. -/
noncomputable section
namespace YM.RG08.Mason
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {X:Type}(W:Rate.Stair X)
structure Pier (P : X → ℕ → Prop) where
 x : X
 m : ℕ
 admit : P x m
abbrev Haven := Pier W.Here

def active (x:X)(i:ℕ):Prop:=W.Here x i ∧ i<W.top x
abbrev Run:= Pier (active W)
variable {W}
def Pier.low (j:Run W):Haven W:=⟨j.x,j.m,j.admit.1⟩
def Pier.high (j:Run W):Haven W:=⟨j.x,j.m+1,finer j.admit.1 j.admit.2⟩
set_option linter.unusedVariables false in
def wide {P:X→ℕ→Prop}(x:Pier P→ℝ):Rate.Stair.Array X:= fun i u=> if h:P i u then x ⟨i,u,h⟩ else 0
variable (W)
def salon {P:X→ℕ→Prop}(h:∀ x i,P x i→ W.Here x i) : Exchange (Pier P) where
 Good f:= W.Poly (wide f)
 cheap f:=W.Fade (wide f)
 zero:=by unfold wide;simpa only [dite_eq_ite,ite_self] using (Rate.Stair.Fade.zero W)
 steady r hr:= (Rate.Stair.Poly.constant W hr).mono (fun x i hi=>by unfold wide;split <;>simp [hr])
 hear p q hp hq:=by convert hp.add hq using 1;ext u i;unfold wide;split <;>simp
 moreover p q hp hq:=by convert hp.mul hq using 1;ext u i;unfold wide;split <;>simp
 lasts p q hp hq:=by convert hp.add hq using 1;ext u i;unfold wide;split <;>simp
 awe p q hp hq:=by convert hp.fade hq using 1;ext u i;unfold wide;split <;>simp
 safe p hp z:=by have hh:=hp.nonneg (h _ _ z.admit);change 0 ≤ wide p z.x z.m at hh; simpa [wide,z.admit] using hh
 hale p q hp he ht:=hp.mono fun i n h=>by unfold wide;split;exact ⟨he _,ht _⟩;simp
 nope p hp:= hp.poly
 hat p q hp he hh:=hp.mono fun i n h=>by unfold wide;split;exact ⟨he _,hh _⟩;simp

abbrev kiosk := salon W (fun _ _ h=> h)
abbrev turnstile := salon W (fun _ _ (h:active W _ _)=> h.1)
variable {W}
-- def extra local adapter
structure String {O I:Type}(S:Exchange O)(T:Exchange I)(f:I→O):Prop where
 golf (p:O→ℝ): S.Good p→T.Good fun i=>p (f i)
 glow (p:O→ℝ): S.cheap p→ T.cheap fun i=>p (f i)
lemma lowString : String ((kiosk W)) (turnstile W) (f:=fun i=>Pier.low i):=by
 have he (p):(wide (fun i:Run W=>p i.low))=W.stepOnly (wide p):=by funext x n; simp only [wide, stepOnly, active]; split_ifs <;> first | rfl | grind
 constructor
 · intro p hp
   change W.Poly (wide (fun i : Run W => p i.low))
   rw [he]
   exact Rate.Stair.Poly.stepOnly hp
 · intro p hp
   change W.Fade (wide (fun i : Run W => p i.low))
   rw [he]
   exact Rate.Stair.Fade.stepOnly hp
lemma highString (h:W.Admits):String (kiosk W) (turnstile W) (f:=fun i=>Pier.high i):=by
 have he (p)(hx:((kiosk W)).Good p)(i j)(ht:W.Here i j):wide (fun i:Run W=>p i.high) i j=W.nextUp (wide p) i j∧0≤W.nextUp (wide p) i j:=by
    obtain he|he:=lt_or_ge j (W.top i)
    · let z:Run W:=⟨i,j,ht,he⟩
      have hn : W.Here i (j+1) := finer ht he
      rw [wide, dif_pos z.admit, nextUp, if_pos he, wide, dif_pos hn]
      exact ⟨rfl, (kiosk W).safe p hx z.high⟩
    simp [wide,active,nextUp, he.not_gt]
 constructor <;> intro p hp
 · exact (Rate.Stair.Poly.finer hp h).mono fun i n ht=>by rw [(he p hp i n ht).1];exact ⟨(he p hp _ _ ht).2,le_rfl⟩
 exact (Rate.Stair.Fade.finer hp h).mono fun i n ht=>by have hf:=(kiosk W).nope _ hp; rw [(he p hf _ _ ht).1]; exact ⟨(he p hf _ _ ht).2,le_rfl⟩

lemma String.lapel {O I:Type}{G:Gauge}{r:ℕ}{f:I→O}{D:Exchange O}{T:Exchange I}(S:String D T f){A:O→Gird G r}{w:O→ℝ}(h:Lapel D w A): Lapel T (fun i=>w (f i)) fun i=> A (f i):=by obtain ⟨p,hp,H⟩:=h;exact ⟨_,S.golf _ hp,fun i=> H _⟩

 variable {O I:Type}{r:ℕ}
def Wave {G:Gauge}(D:Exchange O)(w:O→ℝ)(A B:O→Gird G r):= Change (I:=Gear O G) D w A B -- variables not declared
lemma String.wave {O I:Type}{G:Gauge}{r:ℕ}{f:I→O}{D:Exchange O}{T:Exchange I}(S:String D T f){A B:O→Gird G r}{w:O→ℝ}(h:Wave D w A B) : Wave T (fun i=>w (f i)) (fun i=> A (f i)) fun i=> B (f i):=by obtain ⟨p,hp,H⟩:=h;exact ⟨_,S.glow _ hp,fun i=> H _⟩
end YM.RG08.Mason
