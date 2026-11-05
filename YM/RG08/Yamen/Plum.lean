import YM.RG08.Yamen.Ballot
/-! # Install the paid stage on quantitative laws. -/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}{G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{W:Rate.Stair O}{E e r:ℕ}
variable (K:Wheelhouse a E W)(L:Supplies F P Z)
def gift (P X:MapPrices) (Z:ChartRatio G)(a:Levels G)(i:ℕ):ℝ:=stamp G P X a.clock.kernel Z (RG08.Supplies.stone a i)
def Funds (P X:MapPrices) (Z:ChartRatio G)(a:Levels G)(W:Rate.Stair O):Prop:= (kiosk W).Good fun i=>Yamen.gift P X Z a i.m
def pay (P X:MapPrices) (Z:ChartRatio G)(a:Levels G)(i:Run W):ℝ:=Yamen.gift P X Z a i.m
private lemma pol (h:Yamen.Funds P X Z a W):(turnstile W).Good (pay P X Z a):=lowString.golf _ h
def juniors (a:Levels G)(i:Run W):=a.clock.J i.m
def seniors (a:Levels G)(i:Run W):=a.clock.J (i.m+1)
local notation "T"=>Yamen.charter P X Z K
local notation "D"=> turnstile W
lemma postpaid (i:Run W): Posts G P X a.clock.kernel Z (Yamen.seniors a i) ((T).patch i) (pay P X Z a i):=stamped G P X a.clock.kernel Z (RG08.Supplies.stone a i.m)
variable (hM:Bill G P X a)(hh:Yamen.Funds P X Z a W)
include K hM
omit hM in
lemma regulate (he:e≤ E)(i:Run W): e ≤ juniors a i ∧ juniors a i ≤ Yamen.seniors a i:=⟨he.trans (K.walls i.low),a.fits.mono (by omega)⟩
include hh
lemma commerce (he:e ≤ E)(hr:Live r e)(_hE:0<e): Reckons D ((T).patch) ((T).learn) (coats (T).warp) (needs (T).warp e r) e r (T).branch Z:=by
 have hx:=pol hh
 have hs(i:Run W):=stamped G P X a.clock.kernel Z ((T).patch i)
 refine ⟨⟨fun i=>⟨((T).warp i).tall e r,(honesty_small G P X a.clock.kernel (a.clock.J i.m) e).trans (trod_below ..)⟩,fun i p x=>((lamp P X a (x.m+1)).tag i p).1,fun i p hi hp x=> ?_,?_,?_,?_⟩,fun i p x=> (((T).warp x).tag i p).1,?_,fun i p hI hp x=> compulsory G P X a.clock.kernel (a.clock.J x.m) hI p hp⟩
 · have ht:= regulate K he x;apply (met hM x.m).stars e r i (ht.1.trans ht.2) hr.1 (hi.trans (ht.1.trans ht.2)) p hp
 · intro k hk i p hi hp
   refine (D).hale _ _ hx (fun x=>poem_pos ..) (fun x=>?_)
   have ht:=regulate K he x; exact (hs x).stamps (Yamen.seniors a x) le_rfl i (hi.trans (ht.1.trans ht.2)) p hp k (hk.trans (Nat.add_le_add_right (ht.1.trans ht.2) 2))
 · intro k hk; refine (D).hale _ _ hx (fun x=>le_max_left ..) (fun x=> max_le ((D).safe _ hx x) ?_ )
   have ht:=regulate K he x; exact (le_abs_self _).trans ((hs x).winds (juniors a x) ht.2 e (ht.1.trans ht.2) r hr.1 k (hk.trans (Nat.add_le_add_right (ht.1.trans ht.2) 2)) ((T).branch x))
 · intro k hk; refine (D).hale _ _ hx (fun x=> le_max_left ..) (fun x=> max_le ((D).safe _ hx x) ?_)
   have ht:=regulate K he x; exact (le_abs_self _).trans ((hs x).season (juniors a x) ht.2 e (ht.1.trans ht.2) r hr.1 k (hk.trans (Nat.add_le_add_right (ht.1.trans ht.2) 2)))
 intro i p hi hp;refine (D).hale _ _ hx (fun x=> poem_pos ..) (fun x=>?_)
 have ht:=regulate K he x; exact (hs x).stamps (juniors a x) ht.2 i (hi.trans (ht.1.trans ht.2)) p hp _ (show RG08.Mount.rank r ≤ Yamen.seniors a x +2 from Nat.add_le_add_right (hr.1.trans (ht.1.trans ht.2)) 2)

variable {N:O→ℕ}(hi:∀ i:O,W.top i ≤ N i)
include hi L

def nose (P X:MapPrices)(a:Levels G)(i:Run W):ℝ:=basis G P X a.clock.kernel (a.clock.J i.m)
omit hi L hM in
lemma noses : (D).Good (nose P X a):= (D).hale _ _ (pol hh) (fun i=>basis_nn ..) fun x=> (postpaid (X:=X) (Z:=Z) K x).base _ (regulate K (e:=0) (by omega) x|>.2) -- args
local notation "S"=>Yamen.Act F X hg Z K N hi L
def realmap (he:e ≤ E)(hr:Live r e)(hE:0<e):Pay S (T).branch D (T).learn e r where
 τ x:= brim P (Yamen.seniors a x) (juniors a x)
 ζ:=nose P X a
 x i:= allotment P (Yamen.seniors a i) (juniors a i)
 loan := commerce K hM hh he hr hE
 heroes:=by
    let j(i):= juniors a (i:Run W);let k(i:Run W):=Yamen.seniors a i
    have hJ (i:Run W):j i ≤ k i:= (regulate K he i).2
    have h1 (i:Run W):e ≤ k i:=(regulate K he i).1.trans (hJ i)
    have h2 (i:Run W):= atlas_here (H:=F) L.housed r (shoulders _ hi i)
    have h3 (i:Run W): 0≤ allotment P (k i) (j i):=(h2 i).nonneg
    refine ⟨fun i=>?_,fun i=>h2 i,fun i=>pass_response _ _ _,noses K (Z:=Z) hh, ?_,?_⟩
    · obtain ⟨_,ht,hK,hq⟩:=met hM i.m
      have hi : k i=j i ∨ k i=j i+1:=stepN i.m
      have ⟨hu,hv⟩:=curvature (G:=G) (P:=P) (X:=X) (K:=a.clock.kernel) (j i) hr.1
      have he:=brim_credit (G:=G) (P:=P) (X:=X) (K:=a.clock.kernel) hi
      exact ⟨⟨⟨((T).warp i).tall e r,hu.trans he,hv.trans he,ht _ _ (h1 i) hr.1⟩, hK _ _ (h1 i) hr.1⟩,basis_nn ..,h3 i,hq _ _ (h1 i) hr.1⟩
    · exact (D).hale _ _ (pol hh) (fun i=> (((T).warp i).tag _ _).2.2.1) (fun i=> (postpaid (P:=P) (X:=X) (Z:=Z) K i).brew (j i) (hJ i) _ (h1 i) _ hr.1)
    exact (D).hale _ _ (pol hh) (fun i=>coin_nn _ _ _ _ (((T).warp i).tall _ _) ((lamp P X a (i.m+1)).tag e r |>.1) (h3 i)) (fun i=> (le_abs_self _).trans ((postpaid (X:=X) (Z:=Z) K i).token (j i) (hJ i) e (h1 i) r hr.1))
 sure i:=by
    have hh0 := (veils (X:=X) L.housed _ _ hg (shoulders _ hi i).le (fun b=>L.herald _ _ _ (shoulders _ hi i).le)).2
    apply hh0.mono _ le_rfl (fun _=>le_rfl)
    refine (((T).warp i).tag _ _).2.1.trans ((compulsory G P X a.clock.kernel (a.clock.J i.m) hE 0 le_rfl).trans ?_)
    have hx:= (((T).warp i).tag 0 0).1
    change _ ≤ ((T).warp i).coats 0 0
    change ((T).warp i).coats 0 0/ (RG08.Mount.rank 0:ℕ)/32≤_;norm_num [RG08.Mount.rank];linarith
 fence:=by
    have hw i:= warms L.housed (N i.x) i.m (shoulders _ hi (i:Run W))
    have hU(i:Run W):Posts G P X a.clock.kernel Z (Yamen.seniors a i) ((T).patch i) (pay P X Z a i):=postpaid _ _ --
    have he(i:Run W): ∃ v:Clip,∀ n:Side,Floor ((S).fine i) v n (P.η (Yamen.seniors a i)) (P.Ω (Yamen.seniors a i)):=⟨_,L.housed.all _ _ (shoulders _ hi i)⟩
    have ht(i:Run W):((S).fine i).metric.strip (P.α (Yamen.seniors a i)) (P.Ω (Yamen.seniors a i)) :=(L.housed.rows _ _ (shoulders _ hi i)).2.1
    refine arms Z (p:=fun i=>pay P X Z a i) (pol hh) (fun i=>hU i) hw hw he he ht ht (fun i=>Flat.Ω_pos L.housed (i.m+1)) (fun i=>((T).warp i).tall _ _) (fun i=>?_) (fun _=>le_rfl) fun i=>?_
    · exact (honesty_small G P X a.clock.kernel (juniors a i) e).trans (warmth (i:=juniors a i) (j:=Yamen.seniors a i) (stepN i.m))
    unfold Cell.changeK;simp only [sub_self]; exact (Priced.zero _).row
end YM.RG08.Yamen
