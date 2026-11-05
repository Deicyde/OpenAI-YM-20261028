import YM.RG08.Yamen.Knot

/-! # Measurement parallel domain for both cutoff & fine gauge. !-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter Flat
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}{G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{E e r:ℕ}

structure Audience (a:Levels G) (E:ℕ) where
 low :ℕ
 coarse :ℕ
 fine :ℕ
 cover : coarse ≤ fine
 measure :ℕ
 admit: E ≤ a.clock.J low
abbrev Crowd:= Audience a E
def feast (f:Crowd (a:=a) (E:=E)→ℕ):Stair (Audience a E) where
 sched _:=a.S
 low x:=x.low
 top:=f
 k x:=x.measure
 Z x:=Lambda' a x.measure
 Z_nonneg x:=by unfold Lambda' Lambda; have ht:=Real.log_pos (a.fits.delayed x.measure);linarith
abbrev small (a:Levels G) (E:ℕ):= feast (fun x : Audience a E => x.coarse)
abbrev large (a:Levels G) (E:ℕ):= feast (fun x : Audience a E => x.fine)
lemma listed (f:Crowd (a:=a) (E:=E)→ℕ):Wheelhouse a E (feast f):=⟨fun _=>rfl,fun i=>i.x.admit.trans (a.fits.mono i.admit.1)⟩
variable (f:Audience a E→ℕ)
lemma clocked(x:Crowd (a:=a) (E:=E))(i :ℕ):Stair.age (feast f) x i=Flat.clock a.S (Lambda' a) x.measure i:=rfl
include hg in
lemma nutrient (h:Payment G P X Z a):Yamen.Funds P X Z a (feast f):=by
 let W:= feast f
 refine ⟨1+G.slopeConstant,1,(by linarith [G.slopeConstant_pos hg]),fun x i hi=>?_⟩
 have ht:= (hatch h i).trans (universeClock a hg x.measure i)
 have hv:= (stamped G P X a.clock.kernel Z (RG08.Supplies.stone a i)).pos
 change 0≤wide _ x i∧ wide _ x i ≤ _;rw [Mason.wide,dif_pos hi,pow_one,clocked];exact ⟨zero_le_one.trans hv,ht⟩
include hg in
lemma admission (h:Payment G P X Z a): (feast f).Admits:=by
 have ht : (feast f).Poly (wide fun i:Haven (feast f)=>gift P X Z a i.m):=nutrient hg f h
 apply ht.mono
 intro i j hi;rw [wide,dif_pos hi];unfold stepOnly;split <;> rename_i he
 · exact ⟨by change 0 ≤ ((a.S.block j).val:ℝ); positivity,(stamped G P X a.clock.kernel Z (RG08.Supplies.stone a j)).length⟩
 exact ⟨le_rfl,zero_le_one.trans ((stamped G P X a.clock.kernel Z (RG08.Supplies.stone a j)).pos)⟩

lemma drift {U:ℕ→Kernel Flat.Links Flat.Links}{A₀ B₀ c:ℝ}{d k:ℕ}(hq:Quorum (Flat.curve X) U 0 F A₀ B₀ d k c):Earn F (small a E) X Audience.fine:=by
 let W:=small a E
 let p(i:Haven W):= 2*A₀*W.age i.x i.m^d*((a.S.a (W.top i.x)/a.S.a i.m)^c)
 have he:(kiosk W).cheap p:=by
    change W.Fade (wide p)
    refine Rate.Stair.Fade.acquire (d:=d) (by have :=hq.logged; exact mul_nonneg zero_le_two this) hq.positive ?_ -- A choose 2*A₀
    intro x m hm
    rw [wide,dif_pos hm]
    refine ⟨?_, le_refl _⟩
    change 0 ≤ 2 * A₀ * W.age x m ^ d * (a.S.a (W.top x) / a.S.a m) ^ c
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hq.logged)
      (pow_nonneg (zero_le_two.trans (W.age_big x m)) d))
      (Real.rpow_nonneg (div_nonneg (a.S.a_pos _).le (a.S.a_pos _).le) c)
 refine ⟨p,he,fun i=>?_⟩
 let r:=W.age i.x i.m;let q(N):=A₀*r^d*((a.S.a N/a.S.a i.m)^c)
 have ht(N:ℕ)(hN:i.m ≤ N) : RowCost (Flat.curve X (a.clock.J i.m)) 1 (fun x z=> output (F.H N i.m) x z - U i.m x z) (q N):=by
    exact hq.approximates i.x.measure i.m N (Nat.zero_le _) hN
 have hm:= (i.admit.2).trans i.x.cover
 let L:=i.x.fine;let K:=i.x.coarse
 have hr:0 ≤ r:= le_trans (by norm_num) (W.age_big ..)
 have hv:0 ≤ A₀*r^d:=mul_nonneg hq.logged (pow_nonneg hr _)
 have hj(N:ℕ):0 ≤ q N:=mul_nonneg hv (Real.rpow_nonneg (by have := a.S.a_pos i.m; have :=a.S.a_pos N; positivity) c)
 have hx:=subtract_row (ht L hm) (ht K i.admit.2) (hj _) (hj _)
 have hC:(fun x z=> (output (F.H L i.m) x z-U i.m x z)-(output (F.H K i.m) x z-U i.m x z))=Cell.changeK (F.H L i.m) (F.H K i.m):=funext fun x=>funext fun z=>by unfold Cell.changeK;ring
 have HH: q L ≤ q K:=by unfold q;have he := a.S.a_pos L;have hf:=a.S.a_pos i.m;have hh:=hq.positive;gcongr; exact a.S.strictAnti.antitone i.x.cover
 change RowCost _ 1 (Cell.changeK (F.H L i.m) (F.H K i.m)) _
 rw [←hC];exact fun z x=>(hx z x).trans (ENNReal.ofReal_le_ofReal (by change q L+q K ≤ 2*A₀*r^d*((a.S.a K/a.S.a i.m)^c);unfold q at *;linarith))
end YM.RG08.Yamen
