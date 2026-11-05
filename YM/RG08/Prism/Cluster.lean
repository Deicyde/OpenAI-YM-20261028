import YM.RG08.Prism.Sphere
/-!
# Finite cofinal Fk diagram conservation law, consuming only actual Rail real geometry
   receipts on tori. Hair, chorus, gauge histories & κ in the same grouped laws. Does not
   export as infinite/stable lemma yet, for that see Gallery.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson RG Precision Stationary RG08.Line Fold Drum Bloch Laurent Finset Filter Glyph Room Camera Tack Mount MvPolynomial
open Carrel Tree
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {G:Gauge}{s:Calendar G}{m i:ℕ}

section
variable {c f:Side}{S:StepData c f}(F:Forest S.ratio)(A B:Bed){C:Castle G}{Z:ChartRatio G}{O:Type}[Fintype O](t:Lines G c 1→O)
private abbrev jewels (F:Forest S.ratio)(O:Type):= Camera.Raw (Key F G) O
lemma mapped (h:S.patch.Branches S.kernel G)(hZ:LocalRatio Z)(hC:Stable C)(hp:Proceed C A f)(ht:(grace G S F A B).Flourishes):
 let T :=grace G S F A B
 let M:=rescaleFields (implant F A B t)
 ; belt M (Glyph.stock (unveil (inlet h C Z) c))=
    belt M (china h C)+flask (Real.log ∘ trophy F A B t Z) - liftInn (heater T.inside O) - platen (spend T t) (Key F G):=by
 intro T M
 rw [Mount.stock_inlet h hZ C hC,map_sub,map_add,Cairn.smell hZ S (implant F A B t) (uniform F A B t) (seated F A B t)]
 let I:=Key F G; let D:=speak T (fir S) t
 change belt M _+flask _-belt (rescaleFields (modes D)) _=_
 have he:(fun x:Lex F G O=>∑ z:Edge (Site f), Real.log (Z.J (low S (roll (implant F A B t) x) (z.1,coord z.2))))=ᶠ[𝓝 0]_:=fad F A B t hZ
 rw [flask_same he]
 have hh(a:Inn (Epic S.patch G c)): belt (rescaleFields (modes D)) (liftInn a) = liftInn (twistMean D a):=by
    ext e:1;change tap e _=tap e _;rw [mode_cash,Haze.reflected];simp only [tap,PowerSeries.coeff_C,apply_ite (twistMean D),map_zero]
 rw [hh,china_peak t h hC hp ht,map_add,platen]; abel

lemma pluto {I J K:Type}[Fintype I][Fintype J][Fintype K](A:Strip I J)(B:Strip J K)(hA:∀ i,Pace (A i))(hB:∀ i,Pace (B i))(hz:roll A 0=0)(ht:roll B 0=0):
    ((belt (rescaleFields B)).comp (belt (rescaleFields A)))=(belt (rescaleFields (fun i=>A i ∘ roll B)): Port I→ₐ[ℝ] Port K):=by
   have he(i):belt (rescaleFields B) (rescaleFields A i)=rescaleFields (fun j=> A j ∘ roll B) i:=by
      -- h0 A? not supplied. if not A tiny for divided part; wedge constants discrepancy unaffected by tax, roll B tiny; prove by subtract zero. easier require h0.
      unfold rescaleFields
      change belt (rescaleFields B) (Camera.tax 1 (flask (A i)))=Camera.tax 1 (flask _) -- unfold rescaleFields also unfolded B already
      rw [wire_taxes (rescaleFields B) _ _,flask_comp hB ht (hA i)]
      intro j hj; rw [show j=0 by omega,tap,flask,PowerSeries.coeff_mk,Camera.print,show A i 0=0 from congrFun hz i,map_zero]
   rw [switched, funext he]
end
variable {I J U R O Y:Type}[Fintype I][Fintype J][Fintype U][Fintype R][Fintype O][Fintype Y]
-- result with only broad-dim coefficient; transform administrative field order later
-- H mView synthetic, not physical numerator until later matched
def ash (P: Drum I J U) (h:P.Flourishes) (e:J⊕U≃R)(q:U→O)(X : Steam.Grain R): Port (Camera.Raw I O):=platen (spend P q) I + Glyph.pushed (Γ:=press P e) (Haze.mView (morn P.dark (P.direction h) O) (speak P e q)) X
private def Echo (P:Drum I J U) (e:J ⊕U≃R)(X:Steam.Grain R) (q:U→O)(K:Port (Camera.Raw I O))(p:Still (Camera.Raw I O)):=belt (rescaleFields (modes (speak P e q))) (Glyph.stock X)=K+flask (Real.log ∘ p)-liftInn (heater P.inside O)-platen (spend P q) I
private lemma fleets (P:Drum I J U)(h:P.Flourishes) (e:J⊕U≃R)(a:U→Y)(b:U→O)(X:Steam.Grain R)(he:Steam.Eligible X)(hX:waxed X)(L:Strip (Camera.Raw I Y) (Camera.Raw I O))(hL:∀ i,Pace (L i))(hp:roll L 0=0)(ht:silent L)(K:Port (Camera.Raw I O))(Z:Port (Camera.Raw I Y))(p:Still (Camera.Raw I O))(y:Still (Camera.Raw I Y))
 (h1:Pace p)(h2:Pace y)(h3:p 0=1)(h4:y 0=1)(hc:Echo P e X b K p)(hd:Echo P e X a Z y)(hK:K=belt (rescaleFields L) Z)(hP:p=ᶠ[𝓝 0] fun x=> y (roll L x)* |Fold.Peak.rated L x|):
    ∃ q:Camera.Raw I Y→Port (Camera.Raw I O),(∀ i:Y,q (.inr i)=rescaleFields L (.inr i))∧ belt q (ash P h e a X)=ash P h e b X:=by
 let Q:=forges P e a h X he hX;let T:=forges P e b h X he hX
 unfold Echo at hc hd; rw [mode_cash] at hc hd
 exact T.ate Q L hL hp ht p y h1 h2 h3 h4 K Z hc hd hK hP

section fixed
variable {c f:Side}{S:StepData c f}(F:Forest S.ratio)(A B:Bed)
local notation "P" => grace G S F A B
local notation "E" => fir (G:=G) S
local notation "I₀" => Key F G
variable {C:Castle G}{Z:ChartRatio G}

set_option maxHeartbeats 300000 in
theorem fragile (hv:(P).Flourishes) (hh:S.patch.Branches S.kernel G) (hZ:LocalRatio Z)(hc:Proceed C A f)(hs:Stable C)
    (t:Lines G c 1→O)(y:Lines G c 1→Y)
    (L:Camera.Strip (Camera.Raw I₀ Y) (Camera.Raw I₀ O))(hL:∀ a,Pace (L a))(hp:roll L 0=0)(ht:silent L)
    (hg : belt (rescaleFields (implant F A B t)) (china hh C)=belt (rescaleFields L) (belt (rescaleFields (implant F A B y)) (china hh C)))
    (hJ:trophy F A B t Z =ᶠ[𝓝 0] fun x=> trophy F A B y Z (roll L x)* |Fold.Peak.rated L x|): let V:=unveil (inlet hh C Z) c
    ; ∃ q : Camera.Raw I₀ Y→Port (Camera.Raw I₀ O),(∀ i:Y,q (.inr i)=rescaleFields L (.inr i))∧ belt q (ash P hv E y V)=ash P hv E t V:=by
 intro V
 have he:= inlet_eligible hh Z hs
 have hb:Steam.Eligible V:=unveiled_eligible _ he _;have hM:waxed V:=unsealed_wax (legal_inlet hh Z hs) _
 exact fleets P hv E y t V hb hM L hL hp ht _ _ (trophy F A B t Z) (trophy F A B y Z) (trophy_pace F A B t hZ) (trophy_pace F A B y hZ) (trophy_root F A B t hZ) (trophy_root F A B y hZ) (mapped F A B t hh hZ hs hc hv) (mapped F A B y hh hZ hs hc hv) hg hJ
end fixed
end YM.RG08.Prism
