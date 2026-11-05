import YM.RG08.Fete.Oboes
import YM.RG08.Clef.Bravo
/-!
# Fed frames Wake in actual positive link gauge convention. Full stencil truncated rank and
 generator transfer. Denominator accounted BEFORE export by paper `Lobby`. Here NO integration.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fete
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Trill Exterior RG Precision
open scoped Classical ContDiff Topology BigOperators ENNReal Matrix.Norms.Frobenius ComplexConjugate PowerSeries
variable {G:Gauge}{d n p l e D k q i:ℕ}{σ B:ℝ}{S:Finset Cover}
local notation "E"=>Ed G Cover
variable {X:Labels.Frame G d}

lemma live_bond (T:SectionData X)(c:Accent X)(f:Pearl)(x:E→Dig)(n e:ℕ):
 bond (bandF window (ton (astro T c.ear) n) (concert c.test.play)) f x e=loot (concert c.test.play) 0 f * tap e (MvPolynomial.aeval (x ∘ window) (tap n (flask (astro T c.ear)))):=by
 rw [bond,band_pay,flute,←ton_parley _ (Fete.lamp T c.ear), Gallery.melody,tap,map_sum];congr 1
lemma live_range (T:SectionData X)(c:Accent X)(f:Pearl)(x:E→Dig)(i e:ℕ):
 let l:=(X.grades c.ear).2; (∑ k∈range (l+i+1), Weald.bond (encore T c i k) f x e)=loot (concert c.test.play) 0 f * tap e (MvPolynomial.aeval (x ∘ window) (tap (i+l) (flask (astro T c.ear)))):=by
 intro l;rw [sum_eq_single (i+l)]
 · unfold encore;rw [if_pos rfl,live_bond]
 · intro j _ hj;unfold encore;rw [if_neg hj];unfold bond; simp
 intros h;exfalso;apply h;rw [mem_range];omega
lemma live_wake (T:SectionData X)(c:Accent X)(h:Bid.pop T)(f:Pearl)(x:E→Dig)(e:ℕ):
 let l:=(X.grades c.ear).2;tap e (Weald.awaken l (encore T c) f x)=loot (concert c.test.play) 0 f * tap (e+l) (Gallery.breath (x ∘ window) (flask (astro T c.ear))):=by
 intro l;rw [tap,Weald.awaken,PowerSeries.coeff_mk]; have HL(i): (∑ k∈range (l+i+1),Weald.bond (encore T c i k) f x (e-i))=loot (concert c.test.play) 0 f * tap (e-i) (MvPolynomial.aeval (x ∘ window) (tap (i+l) (flask (astro T c.ear)))):=live_range ..
 simp_rw [HL];rw [←mul_sum];congr 1
 let v:=x ∘ window (G:=G) (S:=T.stencil)
 let F:=astro T c.ear
 let u(n i:ℕ):= tap i (MvPolynomial.aeval v (tap n (Camera.flask F)))
 change (∑ i∈range (e+1),u (i+l) (e-i)) = tap (e+l) (breath v _)
 rw [pulses,show e+l+1=l+(e+1) from by omega,Finset.sum_range_add (n:=l) (m:=e+1),Finset.sum_eq_zero (s:=range l)];swap
 · intro j hj; have hr:= mem_range.mp hj
   change tap _ (MvPolynomial.aeval v (tap j (Camera.flask F)))=_
   rw [flute,←ton_parley F (Fete.lamp T _),show ton F j=0 from ?_,parley_zero,map_zero,tap,map_zero]; ext i; unfold ton;rw [silence T c.ear h _ hr];rfl
 rw [zero_add];apply sum_congr rfl;intro i hi;have hz:=mem_range.mp hi;unfold u;rw [Nat.add_comm i l,show e+l-(l+i)=e-i from by omega] -- mismatch subtraction uses e+l-

-- locator maps. node sign B. actual matrix exp/log composition, germ only
abbrev Players (G:Gauge)(S:Finset Cover):= Matin G S ⊕ (S × G.ColorIndex)
def rivet (i:Matin G S) : foil G→Players G S := fun p=> if p.1=0 then .inl (i.1,p.2) else if p.1=1 then .inr (Place.first i.1,p.2) else .inr (Place.last i.1,p.2)
local notation "I"=>Matin G S
local notation "J"=>Players G S
def cleared (G:Gauge)(S:Finset Cover):Strip (Matin G S) (Players G S):=fun i x=>x (.inl i)
-- couples f σ on outputs after conditional mean relation

def keyed (w:G.El)(S:Finset Cover): Strip (Matin G S) (Players G S):=fun i x=>(Quarry.hot w).fare (window i).2 (x ∘ rivet i)
-- S implicit hygienic: binder S explicit leaks w.
lemma rolled (w:G.El)(i:I):Pace (keyed w S i):= ((Quarry.hot w).fit _).comp (0:Cellar J) (contDiffAt_pi.mpr (fun j=> (contDiff_apply ℝ ℝ (rivet i j)).contDiffAt))
lemma keyed_zero (w:G.El)(S:Finset Cover) : roll (keyed w S) 0=0:=funext fun i=>(Quarry.hot w).origin (window i).2

def member (q:Cellar J)(x:S):G.Color:= heavy G (fun i=>q (.inr (x,i)))
def principal (q:Cellar J)(k:Spot S):G.Color:=heavy G (fun i=>q (.inl (k,i)))
def toTrip (x:Spot S)(q:Cellar J):Quarry.Trip G:=(principal q x,member q (Place.first x),member q (Place.last x))
lemma composed (x:Spot S)(q:Cellar J)(i:G.ColorIndex):Quarry.jaw (q ∘ rivet (x,i))=toTrip x q:=by
 apply Prod.ext;ext j;change q (rivet (x,i) (0,j))=q (.inl (x,j));rw [rivet,if_pos rfl]
 apply Prod.ext <;> ext j
 · change q (rivet (x,i) (1,j))=q _; unfold rivet;dsimp only;simp
 change q (rivet (x,i) (2,j))=q _; unfold rivet;dsimp only;simp
lemma trip_key (w:G.El)(q:Cellar J)(k:Spot S): punch G S (roll (keyed w S) q) k=Quarry.flourish w (toTrip k q).1 (toTrip k q).2.1 (toTrip k q).2.2:=by
 ext i
 change Quarry.glaze w i (Quarry.jaw (q ∘ rivet (k,i)))=_;rw [composed];rfl
lemma trip_live (x:Spot S) : Continuous (toTrip (G:=G) x):=by
 have h(k:Spot S):Continuous (fun z:Cellar J=>principal z k):=(heavy G).continuous.comp (continuous_pi fun _=>continuous_apply _)
 have he(k:S):Continuous (fun z:Cellar J=>member z k):=(heavy G).continuous.comp (continuous_pi fun _=>continuous_apply _)
 exact (h x).prodMk ((he _).prodMk (he _))
@[simp] lemma trip0 (x:Spot S): toTrip x (0:Cellar J)=0:=rfl
lemma gas (w:G.El): ∀ᶠ (x:Quarry.Trip G) in 𝓝 0, G.lieExp (Quarry.flourish w x.1 x.2.1 x.2.2)=gaugeIn w x.1 x.2.1 x.2.2:=by
 let V (x:Quarry.Trip G):=gaugeIn w x.1 x.2.1 x.2.2
 have he : Tendsto V (𝓝 0) (𝓝 1):=by
    have hx:=G.lieExp_cont
    have h : Continuous V:=continuous_const.mul (((hx.comp continuous_snd.fst.neg).mul (hx.comp continuous_fst)).mul (hx.comp continuous_snd.snd)) |>.mul continuous_const
    have hp:V (0:Quarry.Trip G)=1:=by simp [V,gaugeIn]
    rw [←hp];exact h.tendsto _
 filter_upwards [he.eventually G.plog_right,Quarry.colored w] with x hv hx;rw [←hx]; exact hv
lemma castEdge (w:G.El)(i:Spot S):∀ᶠ(q:Cellar J) in 𝓝 0, pore (punch G S (roll (keyed w S) q)) (placeEdge i)=gaugeIn w (principal q i) (member q (Place.first i)) (member q (Place.last i)):=by
 have ht:Tendsto (toTrip i) (𝓝 (0:Cellar J)) (𝓝 0):=by rw [← trip0 (G:=G) i]; exact (trip_live _).tendsto _
 filter_upwards [ht.eventually (gas w)] with q h;rw [pore_site,trip_key];exact h
lemma cast_announce (w:G.El)(T:SectionData X)(Ho:Hol G)(h:T.Sound Ho)(a:X.Index): astro T a ∘ roll (keyed w T.stencil) =ᶠ[𝓝 0] astro T a ∘ roll (cleared G T.stencil):=by
 let S:=T.stencil
 filter_upwards [eventually_all.mpr (fun i:Spot S=>castEdge w i)] with q hq
 let U:=pore (S:=T.stencil) (punch G T.stencil (roll (cleared G T.stencil) q))
 let v(s:Cover):G.El:=if hw:s∈S then w*G.lieExp (- member q (⟨s,hw⟩:S)) else 1
 let F:=T.evaluate (Place.copy X a)
 have he:F (pore (punch G T.stencil (roll (keyed w T.stencil) q)))=F (Lattice.gauge v U):=by
    apply T.cylinder_local;intro p hL hR
    let i:Spot S:=⟨(⟨p.1,hL⟩,p.2),hR⟩
    rw [show pore _ p=pore (punch G T.stencil (roll (keyed w T.stencil) q)) (placeEdge i) from rfl,hq i]
    have hx: principal q i= punch G T.stencil (roll (cleared G T.stencil) q) i:=rfl
    have hh(i:↥S): v i.val=w*G.lieExp (-member q i):=dif_pos i.property
    unfold Lattice.gauge gaugeIn; change w*_ * _=v (Place.first i).val * U (placeEdge i)*(v (Place.last i).val)⁻¹
    rw [hh,hh,_root_.mul_inv_rev, Work.F03.exp_neg_color, Work.F03.exp_neg_color,inv_inv, show U (placeEdge i)=_ from pore_site ..,←hx]; group -- exp neg target whichever
 exact congrArg Complex.re (he.trans (h.gaugeInvariant (Place.copy X a) ..))

def pool (S:Finset Cover)(x:E→Dig)(q:Nd G Cover→Dig)(i:Players G S):=Sum.elim (fun i=>x (window i)) (fun i=> q (i.1.val,i.2)) i
lemma wag (x:E→Dig)(b:Nd G Cover→Dig)(i:I): pool S x b ∘ rivet i= Weald.paint x b ∘ jab (Quarry.hot (1:G.El)) (window i):=by
 funext v;unfold pool Function.comp Weald.paint jab Quarry.hot menu rivet
 dsimp only
 split_ifs with h ht -- dup equal
 · change x _=x _;simp [window]
 · change b _=b _;simp [window,Place.first]
 change b _=b _; simp [window,Place.last]
lemma gas_pay (T:SectionData X)(Ho:Hol G)(h:T.Sound Ho)(a:X.Index)(w:G.El)(x:E→Dig)(b:Nd G Cover→Dig):
 Gallery.breath (gain w x b ∘ window) (flask (astro T a))=Gallery.breath (x ∘ window) (flask (astro T a)):=by
 let S:=T.stencil;let v:=pool S x b
 let c:=cleared G S;let k:=keyed w S
 have H:= flask_same (cast_announce w T Ho h a)
 have hK(i):Pace (k i):= rolled w i
 have hC(i):Pace (c i):=(contDiff_apply ℝ ℝ _).contDiffAt
 rw [flask_comp hK (keyed_zero w _) (lamp T a),flask_comp hC rfl (lamp T a)] at H
 have hp:= congrArg (Gallery.breath v) H
 rw [fugue,fugue] at hp
 rw [show (fun i=> breath v (rescaleFields (cleared G T.stencil) i))=x ∘ window from funext (fun i=>by change breath v (eye (fun q=>q (.inl i)))=x _;rw [Quarry.eye_reader,Gallery.bases_x];rfl)] at hp
 have h(i): breath v (rescaleFields (keyed w T.stencil) i)=gain w x b (window i):=by
    unfold rescaleFields keyed; rw [show liftout _ = eye ((fun y=> (Quarry.hot w).fare (window i).2 (y ∘ rivet i))) from rfl,Quarry.eye_chart (rivet i) _ ((Quarry.hot w).fit _) ((Quarry.hot w).origin _),wag];rfl
 rwa [show gain w x b ∘ window=(fun (i:Matin G S)=>breath v (rescaleFields k i)) from funext (fun i=>(h i).symm)]
/-- The canonical chart is called at own coupling over the rooted dictionary,
 incl arbitrary rescaled FPS probes of compact support at any admitted horizon. -/
theorem encore_calls (T:SectionData X)(Ho:Hol G)(h:T.Sound Ho)(ht:Bid.pop T)(c:Accent X):Weald.Calls (X.grades c.ear).2 (encore T c):=by
 intro f x b w; rw [←woken,←woken];ext e:1
 change tap e _=tap e (awaken _ _ _ (gain w x.get b.get));rw [live_wake T c ht f x.get e,live_wake T c ht f (gain w x.get b.get) e,gas_pay T Ho h c.ear];
end YM.RG08.Fete
