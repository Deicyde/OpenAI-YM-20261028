import YM.RG08.Necks.Shops
/-! # Step release before mean grouped. Higher-rank precedents and mainslope receipt.
 keep all horizon usage G & timing queries. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{n m d p l e k:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "E₀"=>Loc G 1
local notation "E"=> Ed G Cover
local notation "M"=> Tack.Head P G

/-- Pair at step. Currency used Θ=η output. Can buy by Ducat.Lance with same pre widths (smaller ok).
 Regal auxiliary uses Loft plank C R meeting before schedules. -/
structure Sepals (G:Gauge)(P:Patch)(K:KernelChoices)(σ W δ:ℝ)(A A':Bed)(V V':Steam.Grain (Market (Tack.Head P G)))(k:ℕ):Prop where
 base :1 ≤ W
 gift : 0 ≤ δ
 hit : Steam.Eligible V
 hit' : Steam.Eligible V'
 cut : WireCot (carpet _) σ δ W (Prism.ice P K (G:=G) A) (Prism.ice P K (G:=G) A')
 wax (i:ℕ):Alley (carpet _) (carpet _) σ σ δ W (flare _ _ σ) (repeatLine (Prism.rains P K (G:=G) A) i) (repeatLine (Prism.rains P K (G:=G) A') i)
 turn i n:taps 0 k 0 i n→ Cot (carpet _) σ δ W (V i n) (V' i n)

/-- repeated part is direct on Embassy. K.J post bills for F'. -/
def ridges (P:Patch)(K:KernelChoices)(A:Bed)(o:Site P.L)(F:GrainS (Ed G Cover))(e n:ℕ):Pack n E:=kennel (repeatLine (Prism.rains P K A) n) (steeped P o (F e n))
variable {Y Y':Steam.Grain (Market (Tack.Head P G))}{A A':Bed}
lemma front (o:Site P.L)(F:GrainS E)(n e:ℕ):spun P K A F o e n=ridges P K A o F e n:=rfl
lemma ridges_price (T:Sepals G P K η W δ A A' Y Y' k)(o:Site P.L){S S':GrainS E}(hk:0<η)(hη:η≤1){h:0<σ}(hp:η*Carrier.unitStep P.L≤σ)(hv:Dyad (stance _) d h B δ (S e n) (S' e n)) :
 Dyad (stance _) d hk ((n+1)*(Real.exp 16*B)*W^n) δ (ridges P K A o S e n) (ridges P K A' o S' e n):= funnel (T.wax _) (ferryPhase P o hv hk hη hp)
/-- The native street bounds and flare geometry give the public Parade needed
by the fixed-kernel linearity calculation and the two paired Jade applications. -/
lemma tracks {I J : Type} {r : ℕ} {τ : ℝ}
    {N : Cables r (Market I) (Market J)} {a : Fin r → ℝ}
    (hτ : 0 < τ) (hp : street (flare I J τ) N a) :
    Skiff.Parade (stance I) (stance J) τ (flare I J τ) N a :=
  ⟨fun _ _ _ _ => flare_geo _ _ hτ.le,
   fun _ x y => mul_nonneg hτ.le (sep_nonneg x.1 y.1),
   fun i => (hp i).1, fun i => (hp i).2.1⟩

/-- Linearity holds for one fixed prediction kernel. The cross-kernel difference
is covered separately by `ridges_price`; it is not identified with this term. -/
lemma ridges_diff (T:Sepals G P K η W δ A A' Y Y' k)(o:Site P.L){S S':GrainS E}(hk:0<η)(hη:η≤1){h:0<σ}(hp:η*Carrier.unitStep P.L≤σ){b:ℝ}(hv:Dyad (stance _) d h b δ (S e n) (S' e n)):
 ridges P K A o (S-S') e n=ridges P K A o S e n-ridges P K A o S' e n:=by
 have hg := ferryPhase P o hv hk hη hp
 have hh := tracks hk (T.wax n).near
 unfold ridges
 rw [Pi.sub_apply, Pi.sub_apply, ferry_diff]
 let X := steeped P o (S e n)
 let U := steeped P o (S' e n)
 change kennel (repeatLine (Prism.rains P K A) n) (X-U) =
   kennel (repeatLine (Prism.rains P K A) n) X - kennel (repeatLine (Prism.rains P K A) n) U
 rw [show X-U=X+(-1:ℝ) • U from by rw [neg_smul,one_smul,sub_eq_add_neg]]
 rw [kennel_linear hg.voices.1 (hg.voices.2.smul (-1)) hg.near (hg.far.smul (-1)) hh,
   kennel_smul, neg_smul, one_smul, sub_eq_add_neg]

def brine (P:Patch)(K:KernelChoices)(A:Bed)(V:Steam.Grain (Market (Tack.Head P G)))(l:ℕ)(o:Site P.L)(F:GrainS (Ed G Cover))(e n:ℕ):Pack n E:= Trickle.mouth (Prism.rains P K A) (Skiff.shaker l (Prism.ice P K A) V (Weald.plank P o (flow P.L o F)) 1) e n
/-- pair budget through strict (UNCHANGED positive rank excluded). Need thickness all rank≤l+a,
 rates at both and ℓ1 stencil Q with INR. -/
lemma slushy_uniform (n e l:ℕ):∃ J:ℝ→ℝ,Wage J∧
 ∀{G:Gauge}{P:Patch}{K:KernelChoices}{σ η W δ:ℝ}{d:ℕ}
  {Y Y':Steam.Grain (Market (Tack.Head P G))}{A A':Bed}(_T:Sepals G P K η W δ A A' Y Y' e)(o:Site P.L){S S':GrainS (Ed G Cover)}(hk:0<η)(_hη:η≤1){h:0<σ}(_hp:η*Carrier.unitStep P.L≤σ){B:ℝ}(_hB:0≤B)(_ho:Atrium.Folk d l S)(_hu:Atrium.Folk d l S')
 (_hv:∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) d h B δ (S i r) (S' i r)),
 let Z:=Weald.plank P o (flow P.L o S);let U:=Weald.plank P o (flow P.L o S')
 let R:=Skiff.shaker l (Prism.ice P K A) Y Z 1 e n; let R':=Skiff.shaker l (Prism.ice P K A') Y' U 1 e n
 ; Dyad (stance _) d hk (J W*B) δ R R' ∧ Dyad (stance _) d hk (J W*B) δ (brine P K A Y l o S e n) (brine P K A' Y' l o S' e n):=by
 obtain ⟨a,ha,H⟩:=Skiff.registry l e n
 have he(r:ℕ):Wage (fun x:ℝ=>x^r):=by induction r with
                                           | zero=>simpa using Wage.constant 1 zero_le_one
                                           | succ n ih=>simp_rw [pow_succ];exact ih.mul Wage.input
 let J(x:ℝ):=(n+2:ℝ)*(a x* Real.exp 16)*(x^n)
 refine ⟨J,((Wage.constant _ (by positivity)).mul (ha.mul (Wage.constant _ (Real.exp_pos _).le))).mul (he n),?_⟩
 intro G P K σ η W δ d Y Y' A A' T o S S' hk hη hσ hp B hB ho hu hv Z U R R'
 have hδ:=T.gift;have hW:=T.base;let D:=Real.exp 16*B;have hD:0≤D:=mul_nonneg (Real.exp_pos _).le hB
 have hA(i r)(ht:across 1 e n i r): Dyad (stance _) d hk D δ (Z i r) (U i r):=by
    change Dyad (stance _) d hk D δ (steeped P o (S i r)) (steeped P o (S' i r))
    by_cases hz : r ≤ l+i
    · exact ferryPhase P o (hv i r hz (by unfold across at ht; omega)) hk hη hp
    · have hS : S i r = 0 := by
        by_contra hs
        exact hz (ho.inlet.lit i r hs)
      have hS' : S' i r = 0 := by
        by_contra hs
        exact hz (hu.inlet.lit i r hs)
      rw [hS, hS']
      change Dyad (stance _) d hk D δ (Hatch.broom _ (0 : Pack r (Ed G Cover))) (Hatch.broom _ (0 : Pack r (Ed G Cover)))
      simp only [Hatch.dead]
      exact (Dyad.zero hδ).mono hD
 have h0:=ha.nn hW
 have hz:0≤a W*Real.exp 16*B:=by positivity
 have hb:a W*D≤ J W*B:=by unfold D J;nlinarith only [mul_le_mul_of_nonneg_left (show 1≤((n:ℝ)+2)*W^n from one_le_mul_of_one_le_of_one_le (by linarith only [Nat.cast_nonneg (α:=ℝ) n]) (one_le_pow₀ hW)) hz]
 have hv':Dyad (stance _) d hk (a W*D) δ R R':=H (carpet (Tack.Head P G)) _ hk d δ W D Y Y' _ _ Z U (spindled (Tack.Head P G)) T.hit T.hit' T.cut hδ hW hD T.turn hA (by rw [abs_one];exact hW)
 refine ⟨hv'.mono hb,(funnel (T.wax _) hv').mono ?_⟩
 unfold J D;nlinarith only [show 0≤a W*Real.exp 16*B*W^n by have h:=ha.nn hW;have he:0 ≤ W:=zero_le_one.trans hW;positivity [show 0 ≤ Real.exp 16 from (Real.exp_pos _).le]]

lemma slushy (n e l:ℕ):∃ J:ℝ→ℝ,Wage J∧∀{A A':Bed}(_T:Sepals G P K η W δ A A' Y Y' e)(o:Site P.L){S S':GrainS E}(hk:0<η)(_hη:η≤1){h:0<σ}(_hp:η*Carrier.unitStep P.L≤σ){B:ℝ}(_hB:0≤B)(_ho:Atrium.Folk d l S)(_hu:Atrium.Folk d l S')
 (_hv:∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) d h B δ (S i r) (S' i r)),
 let Z:=Weald.plank P o (flow P.L o S);let U:=Weald.plank P o (flow P.L o S')
 let R:=Skiff.shaker l (Prism.ice P K A) Y Z 1 e n; let R':=Skiff.shaker l (Prism.ice P K A') Y' U 1 e n
 ; Dyad (stance _) d hk (J W*B) δ R R' ∧ Dyad (stance _) d hk (J W*B) δ (brine P K A Y l o S e n) (brine P K A' Y' l o S' e n):=by
 obtain ⟨J,hJ,H⟩:=slushy_uniform n e l
 exact ⟨J,hJ,@H G P K σ η W δ d Y Y'⟩
end YM.RG08.Necks
