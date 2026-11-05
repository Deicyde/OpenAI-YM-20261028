import YM.RG08.Slate.Spin
/-!
# Centric consumers ask ONLY on unshifted group geometry now.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Slate
open Filter Function Matrix MeasureTheory Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Prism Tack Camera
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {X Y : Type}[Fintype X][Fintype Y]
variable {G: Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(A B:Bed)
variable (v:Lines G c 1→X)(w:Lines G c 1→Y)(g:Cellar X→Cellar Y)(m:Cellar X→ AxisChart G F→AxisChart G F)

lemma uniformCost (x:Lex F G X):represent (tone F A B v x)=F.drape (exposure F 0 (frock F A B v x)):=by
 funext e
 by_cases he:e∈F.trunks
 · rw [Work.F03.represent_link, show F.drape _ e=1 from F.on_tree _ ⟨e,he⟩, show (_,coord e.2)=Pressure.pole e from rfl,tone_trunk F A B v _ _ he, G.mat_lieExp_zero]
 rw [Work.F03.represent_link, show F.drape _ e= _ from F.off_tree (exposure F 0 (frock F A B v x)) ⟨e,he⟩];unfold Work.F05.exposure frock; rw [Precision.link_one,Precision.replica_one];simp; rfl

def borne (z:Cellar X):Bid.Dir G c:=arm G c 1 (z ∘ v)
lemma anchor (x:Lex F G X):flame F A B v x=borne v (envar x):=by
 let P:=grace G S F A B
 have ht:= (speak_zone P (fir S) v x).2
 ext ⟨q,j⟩ l
 exact congrFun ht (q,j,l)

structure Solved (s:Signed)(o:Site c) where
 rates : Cellar X→ House F (G:=G) F
 grip:Pace (uncurry m)
 run0:m 0 0=0
 zoom:Pace g
 fit0:g 0=0
 paid' : ∀ᶠ y:Cellar X × AxisChart G F in 𝓝 0, exposure F 0 (m y.1 y.2)=(rates y.1).arrow (exposure F 0 y.2)
 field:∀ᶠ y:Cellar X × AxisChart G F in 𝓝 0,∃ b:Site f→G.El,
    F.drape ((rates y.1).arrow (exposure F 0 y.2))=Lattice.gauge b (Lattice.pull s (S.ratio.embed o) (F.drape (exposure F 0 y.2))) ∧
    represent (borne w (g y.1))=Lattice.gauge (b ∘ S.ratio.embed) (Lattice.pull s o (represent (borne v y.1)))

variable{s:Signed}{o:Site c}
-- no implicit passes through modified fixture

def certify (M:Solved S F v w g m s o) (Z:ChartRatio G)(hZ:LocalRatio Z):Bore S F A B v w Z where
 logo:=s
 root:=o
 map:=scene S F A B v w g m
 level:= start S F A B v m w g M.fit0 M.run0
 fine i:=contDiffAt_pi.mp (flying S F A B v m w g M.grip M.zoom M.fit0) i
 tags j i:= tranquil S F A B v m w g M.zoom j i
 heritage:=by
    let Q(z:Lex F G X):=(envar z,frock F A B v z)
    have ht:Tendsto Q (𝓝 0) (𝓝 0):= by
       have hi:Q 0=0:=by unfold Q;rw [central];rfl
       simpa only [hi] using! (show Pace Q from smooth2.contDiffAt.prodMk (frock_pace ..)).continuousAt.tendsto
    filter_upwards [ht.eventually M.paid',ht.eventually M.field] with x hx hF
    obtain ⟨t,he,hh⟩:=hF; refine ⟨t,?_,?_⟩
    · rw [uniformCost S,uniformCost S]
      change F.drape (exposure F 0 (frock _ _ _ _ (flight S F A B v m w g x)))= _ -- flight .. fails
      rw [paid, show exposure F 0 (m (envar x) (frock F A B v x)) =_ from hx]; exact he
    rw [anchor S,anchor S];exact hh
 tangle:= duefy S F A B v w g m M.rates hZ M.grip M.zoom M.fit0 M.run0 M.paid'
end YM.RG08.Slate
