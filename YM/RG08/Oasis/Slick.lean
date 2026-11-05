import YM.RG08.Oasis.Tone
/-!
# Film limit carries Ward & label and threshold. Explicit cut distinctions (at a fixed level
an all-orders simultaneous announcement NOT assumed). Caller supplies Cauchy rate as
from Spend at each fixed level. Step compatibility on raw components proved separately.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Oasis
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April Filter Gallery
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
variable {X Z I:Type}{G:Gauge}{D d e n k p:ℕ}{θ:ℝ}{h:0<θ}{L:Jetty.Loom I}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover

lemma shoot_meter (F:Labels.Frame G d){S:ℕ→Pack n E}{T:Pack n E}(hF:∀ᶠ i in atTop,Ready D G n (S i))(hT:Ready D G n T){b:ℕ→ℝ}(hb:Tendsto b atTop (𝓝 0))(hB:∀ᶠ i in atTop,b i ≥0)(hw:∀ᶠ i in atTop,Sings Δ D h (S i - T) (b i))(a:Accent F)(he:n≤d): Tendsto (fun i=>pix F a.ear a.test.play (S i)) atTop (𝓝 (pix F a.ear a.test.play T)):=by
 obtain ⟨C,hC,H⟩:= pitch F D θ h
 have hz := squeeze_zero' (f:=fun i=>|Trill.pix F a.ear a.test.play (S i)- Trill.pix F a.ear a.test.play T|) (g:=fun i=>C*b i) (Eventually.of_forall (fun i=>abs_nonneg _)) (show ∀ᶠ i in atTop, |pix F a.ear a.test.play (S i)-pix F a.ear a.test.play T|≤ C*b i from ?_) (by simpa only [mul_zero] using tendsto_const_nhds.mul hb)
 · exact tendsto_iff_dist_tendsto_zero.mpr hz
 filter_upwards [hF,hB,hw] with i hx hh hp; rw [←pix_minus F hx hT];exact H a n he _ (hx.coherent.sub hT.coherent) _ hh hp
lemma summit_limits {F:ℕ→Pack n I}{T:Pack n I}(he:binge F T)(v:Tray I)(t:Pearl)(i:ℕ):Tendsto (fun j=> tap i (summit (F j) t v)) atTop (𝓝 (tap i (summit T t v))):=by
 unfold tap summit Gallery.volume; simp_rw [map_sum,PowerSeries.coeff_smul];apply tendsto_finsetSum _; intro x _; exact (he x t).mul_const _
variable (F:Labels.Frame G d)
local notation "B0"=> Bouquet F

def plains (S:ℕ→Bouquet F):Bouquet F:=fun i e n=>stage (fun m=>S m i e n)

/-- closure through a fixed meter at a fixed i (width known through e only).
Complement can use Dummy coordinates. Consumer for all n, including older e beyond l.
- strongest cutoff assertion on B-solution per slot yields this. Hol criterion via finite Calls.
-/
lemma storing (S:ℕ→Bouquet F)(s:ℕ){k D:ℕ}(h:0<θ)(hp:∀ i,s ≤ i→Threads D (S i))(hi:∀ i,s ≤ i→Clean F (S i))
 (hQ:∀ i t n,t ≤ k→∃ (C:ℝ)(a:ℕ→ℝ),Tendsto a atTop (𝓝 0) ∧ ∀ m,s ≤ m→0≤ a m∧ Sings Δ D h (S m i t n) C∧ ∀ j,m≤j→Sings Δ D h (S m i t n-S j i t n) (a m)):
 ∀ (y:Accent F)(t:ℕ),t≤k → let u:=octave y; let Y:=plains F S y
                   ; (∀ x:Accent F,Trill.project F Y t x=if y=x∧t=0 then 1 else 0)∧ (∀ (f:Pearl)(v:Tray E)(b:Gallery.Tray (Nd G Cover))(w:G.El), tap t (Weald.mint u Y f v) =tap t (Weald.mint u Y f (portrait (Quarry.hot w) (Quarry.art v b)))) ∧ (∀ n Y', Y'=Y t n→ Ready D G n Y' ∧ (n>u+t→Y'=0)∧ binge (fun i=>S i y t n) Y'):=by
 intro y t ht u Y
 choose C a H hA using hQ
 have H'(m n)(hv:m ≤ k):let s':=fun i=> S i y m n;let T:=Y m n
                  ; binge s' T ∧ Ready D G n T∧∀ i,s ≤ i→Sings Δ D h (s' i-T) (a y m n hv i):=by
    let U:=C y m n hv
    obtain ⟨hT,hs,hL,hS,hd⟩:=stageLimit (d:=D) (L:=Δ) (h:=h) (C:=U) s (H y m n hv) (fun i hi=>(hA y m n hv _ hi).1) (F:=fun i=> S i y m n) (fun i hi=>by have hh := permit_ready (n:=n) (e:=m) (hp i hi y).inlet;exact ⟨hh.coherent,(hA y m n hv i hi).2.1,hh.turned⟩) (fun i j hi hj=> (hA y m n hv _ hi).2.2 j hj)
    refine ⟨hT,⟨hL,hS,θ,h,max 0 U,le_max_left ..,hs.mono le_rfl le_rfl (fun _=>le_rfl) (le_max_right ..)⟩,hd⟩
 have Hm:=Filter.eventually_ge_atTop s
 refine ⟨?_,?_,?_⟩
 · intro x;let v:=octave x
   have hs(m n)(hm:m ≤ k)(hn:n≤d): Tendsto (fun i=>pix F x.ear x.test.play (S i y m n)) atTop (𝓝 (pix F _ _ (Y m n))):=shoot_meter F (h:=h) (hF:=Hm.mono (fun j hj=>permit_ready (hp j hj y).inlet)) (H' m n hm).2.1 (H y m n hm) (Hm.mono (fun j hj=> (hA y m n hm j hj).1)) (Hm.mono (fun j hj=>(H' m n hm).2.2 j hj)) x hn
   apply tendsto_nhds_unique (f:=fun i=> Trill.project F (S i y) t x) ?_ (tendsto_const_nhds.congr' (Hm.mono (fun j hj=>(clean_value F (S j) (hi j hj) _ _ _).symm)))
   unfold project;apply tendsto_finsetSum _;intro i hi;split
   · -- rw? split target if in both lambda; simp
     rename_i he
     simpa only [he,ite_true] using (hs (t-((F.grades x.ear).2-i)) i (by omega) (by change i∈range (v+1) at hi; rw [mem_range] at hi; have hv:v ≤ d:= octave_le x;omega))
   exact tendsto_const_nhds
 · -- finite Gauge shelves. strong Θ
   intro f v b w;let r:=portrait (Quarry.hot w) (Quarry.art v b)
   have hp'(z:Tray E):Tendsto (fun i=>tap t (Weald.mint u (S i y) f z)) atTop (𝓝 (tap t (Weald.mint u Y f z))):=by
      simp_rw [Atrium.scripted];apply tendsto_finsetSum _;intro i hi;apply tendsto_finsetSum _;intro n _;exact summit_limits (H' _ n (Nat.le_trans (by simpa only [mem_range,Nat.lt_succ_iff] using hi) ht)).1 z f _
   apply tendsto_nhds_unique (hp' v) ((hp' r).congr' (Hm.mono fun i hi=> congrArg (tap t) ((hp i hi y).outlet f v b w).symm))
 intro n y' hh;subst y';refine ⟨(H' t n ht).2.1,fun hi=>?_,(H' t n ht).1⟩
 funext i f; exact tendsto_nhds_unique ((H' t n ht).1 i f) (tendsto_const_nhds.congr' (Hm.mono fun j hj=>by change (0:Pack n E) i f= S j y t n i f; rw [show S j y t n=0 from Classical.not_not.mp (fun h=>by have hh:= (hp j hj y).inlet.lit _ _ h;change n>octave y + t at hi;omega)]))
end YM.RG08.Oasis
