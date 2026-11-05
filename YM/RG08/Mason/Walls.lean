import YM.RG08.Mason.Hike

/-! # Event grading uniform domain. horizon E fixed. all lanes irrespective packet arity.
 Vac scalar untouched. H entry joint smoothing through admitted overlap. !-/
noncomputable section
namespace YM.RG08.Mason
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {X:Type}(W:Rate.Stair X){G:Gauge}

abbrev Frame := X → ℕ→ Yard G
-- Frame W unused; result calc choose explicit binder

def learn (H:X→ℕ→Yard G):Run W→Yard G:=fun i=> H i.x i.m
def apron (H:X→ℕ→Yard G)(e r:ℕ):X→ℕ→ℝ:=fun i m=> (H i m).coats e r
def upcoming (H:X→ℕ→Yard G)(e r:ℕ):Run W→ℝ:=fun i=> apron H e r i.x (i.m+1)

structure Charter (K:RG.KernelChoices)(Z:ChartRatio G) where
 patch: Run W→Patch
 same i : ((patch i).L.val:ℝ)=W.length i.x i.m
 branch :∀ i,(patch i).Branches K G
 yard:X→ℕ→ Yard G
namespace Charter
variable {K:KernelChoices}{Z:ChartRatio G}{W} (T:Charter W K Z)
abbrev warp := Mason.learn W T.yard
abbrev learn := upcoming W T.yard
end Charter
variable {W}{K:KernelChoices}{Z:ChartRatio G}
structure Pros (T: Charter W K Z) where
 side : SliceSide T.patch T.warp K Z
 current : X→ℕ→Castle G
 receipt :∀ i:Run W,side.letters i=current i.x (i.m+1)

variable (hg:G.Simple)
structure Vow (E:ℕ){T:Charter W K Z}(R:Pros T) where
 tuition (e r:ℕ): e ≤ E→Live r e→0<e→Pay R.side T.branch (turnstile W) T.learn e r
 agreement : ∀ i:Run W,R.current i.x i.m=R.side.car hg T.branch i
 base : Lapel (r:=0) (kiosk W) (fun i=>apron T.yard 0 0 i.x i.m) fun i=>R.current i.x i.m 0 0
 baseC: Lapel (r:=0) (turnstile W) (coats T.warp 0 0) R.side.top
 trench (e r): e ≤ E→Live r e→ 0<e→ ∃ p,(kiosk W).Good p ∧ ∀ i:Haven W,i.m=W.top i.x→ Held (carpet _) (apron T.yard e r i.x i.m) (p i) (R.current i.x i.m r e)

def Known {T:Charter W K Z}(R:Pros T)(e r:ℕ):Prop:=Lapel (kiosk W) (fun i=>apron T.yard e r i.x i.m) fun i=>R.current i.x i.m r e
def Signs {T:Charter W K Z}(R:Pros T)(e r:ℕ):Prop:= Lapel (turnstile W) (coats T.warp e r) fun i=>R.side.ample T.branch i r e
lemma up {T:Charter W K Z}{R:Pros T}{e r:ℕ}(h:W.Admits)(hk:Known R e r): Lapel (turnstile W) (T.learn e r) fun i=> R.side.letters i r e:= by simp_rw [R.receipt];exact (highString h).lapel hk
variable {T:Charter W K Z}{E e r:ℕ}

def merit (E e r:ℕ):=e*(E+1)+(E-r)
lemma precedes (h:e ≤ E)(hf:Live r e){i j:ℕ}(he: Earlier e r i j):merit E i j < merit E e r:=by
 have hb := he.1.1
 rcases he.2 with hi|⟨rfl,hz⟩
 · unfold merit;have hx:(i+1)*(E+1) ≤ e*(E+1):= Nat.mul_le_mul_right _ hi; rw [Nat.add_mul] at hx;omega
 unfold merit;have he:=hf.1;omega

theorem delivers (R:Pros T)(h:W.Admits) (he:Vow hg E R)(hC:e ≤ E)(hK:Live r e):Known R e r ∧ Signs R e r:=by
 generalize hp:merit E e r=n
 induction n using Nat.strong_induction_on generalizing e r with
 | h n ih=>
   rcases eq_or_lt_of_le (Nat.zero_le e) with h0|hz
   · subst e;have hr:=hK.1; have heq:r=0:=by omega
     subst r
     exact ⟨he.base,he.baseC⟩
   have older i j (ht:Earlier e r i j):Known R i j ∧ Signs R i j:= ih _ (hp ▸ precedes hC hK ht) (by have h:=ht.2;omega) ht.1 rfl
   obtain ⟨p,s,hp',hs,H⟩:=hires hg R.side (he.tuition e r hC hK hz) hK hz (fun i t h'=> up h (older i t h'|>.1)) (fun i t h=> (older _ _ h).2)
   obtain ⟨t,ht,Ht⟩:=he.trench e r hC hK hz
   let D:=apron T.yard e r
   have hx : Known R e r:=ribs (W:=W) (F:=fun x i=> R.current x i r e) (w:=D) ht hp' Ht (fun i b hb ht=>by
      rw [← T.same i, he.agreement i] -- implicit i.low agree
      exact (H i b hb (R.receipt i ▸ ht : Held (carpet _) (T.learn e r i) b (R.side.letters i r e))).1)
   obtain ⟨a,ha,hU⟩:=up h hx
   let W':=turnstile W
   exact ⟨hx,_,W'.hear _ _ (W'.moreover _ _ hs ha) hs,fun i=>(H i (a i) (W'.safe _ ha i) (hU i)).2.1⟩
end YM.RG08.Mason
